open Core
open! Import
open Types.Internal_observer

module Packed_ = struct
  include Types.Internal_observer.Packed

  let sexp_of_t (T internal_observer) =
    internal_observer.observing |> [%sexp_of: _ Types.Node.t]
  ;;

  let prev_in_all (T t) = t.prev_in_all
  let next_in_all (T t) = t.next_in_all
  let set_prev_in_all (T t1) t2 = t1.prev_in_all <- t2
  let set_next_in_all (T t1) t2 = t1.next_in_all <- t2
end

module State = struct
  type t = Types.Internal_observer.State.t =
    | Created
    | In_use
    | Disallowed
    | Unlinked
  [@@deriving sexp_of]
end

type 'a t = 'a Types.Internal_observer.t =
  { (* State transitions:

       {v
         Created --> In_use --> Disallowed --> Unlinked
           |                                     ^
           \-------------------------------------/
       v} *)
    mutable state : State.t
  ; observing : 'a Node.t
  ; mutable on_update_handlers : 'a On_update_handler.t list
  ; (* [{prev,next}_in_all] doubly link all observers in [state.all_observers]. *)
    mutable prev_in_all : Packed_.t or_null
  ; mutable next_in_all : Packed_.t or_null
  ; (* [{prev,next}_in_observing] doubly link all observers of [observing]. *)
    mutable prev_in_observing : ('a t[@sexp.opaque]) or_null
  ; mutable next_in_observing : ('a t[@sexp.opaque]) or_null
  }
[@@deriving fields ~getters ~iterators:iter, sexp_of]

type 'a internal_observer = 'a t [@@deriving sexp_of]

let incr_state t = t.observing.state

let use_is_allowed t =
  match t.state with
  | Created | In_use -> true
  | Disallowed | Unlinked -> false
;;

let same (t1 : _ t) (t2 : _ t) = phys_same t1 t2
let same_as_packed (t1 : _ t) (Packed_.T t2) = same t1 t2

let invariant invariant_a t =
  Invariant.invariant t [%sexp_of: _ t] (fun () ->
    let check f = Invariant.check_field t f in
    Fields.iter
      ~state:ignore
      ~observing:(check (Node.invariant invariant_a))
      ~on_update_handlers:
        (check (fun on_update_handlers ->
           match t.state with
           | Created | In_use | Disallowed -> ()
           | Unlinked -> assert (List.is_empty on_update_handlers)))
      ~prev_in_all:
        (check (fun prev_in_all ->
           (match t.state with
            | In_use | Disallowed -> ()
            | Created | Unlinked -> assert (Or_null.is_null prev_in_all));
           if Or_null.is_this prev_in_all
           then
             assert (
               same_as_packed
                 t
                 (Or_null.value_exn (Packed_.next_in_all (Or_null.value_exn prev_in_all))))))
      ~next_in_all:
        (check (fun next_in_all ->
           (match t.state with
            | In_use | Disallowed -> ()
            | Created | Unlinked -> assert (Or_null.is_null next_in_all));
           if Or_null.is_this next_in_all
           then
             assert (
               same_as_packed
                 t
                 (Or_null.value_exn (Packed_.prev_in_all (Or_null.value_exn next_in_all))))))
      ~prev_in_observing:
        (check (fun prev_in_observing ->
           (match t.state with
            | In_use | Disallowed -> ()
            | Created | Unlinked -> assert (Or_null.is_null prev_in_observing));
           if Or_null.is_this prev_in_observing
           then
             assert (
               phys_equal
                 t
                 (Or_null.value_exn
                    (next_in_observing (Or_null.value_exn prev_in_observing))))))
      ~next_in_observing:
        (check (fun next_in_observing ->
           (match t.state with
            | In_use | Disallowed -> ()
            | Created | Unlinked -> assert (Or_null.is_null next_in_observing));
           if Or_null.is_this next_in_observing
           then
             assert (
               phys_equal
                 t
                 (Or_null.value_exn
                    (prev_in_observing (Or_null.value_exn next_in_observing)))))))
;;

let value_exn t =
  match t.state with
  | Created -> failwiths "Observer.value_exn called without stabilizing" t [%sexp_of: _ t]
  | Disallowed | Unlinked ->
    failwiths "Observer.value_exn called after disallow_future_use" t [%sexp_of: _ t]
  | In_use ->
    let uopt = t.observing.value_opt in
    if Or_null.is_null uopt
    then failwiths "attempt to get value of an invalid node" t [%sexp_of: _ t];
    Or_null.unsafe_value uopt
;;

let on_update_exn t on_update_handler =
  match t.state with
  | Disallowed | Unlinked -> failwiths "on_update disallowed" t [%sexp_of: _ t]
  | Created | In_use ->
    t.on_update_handlers <- on_update_handler :: t.on_update_handlers;
    (match t.state with
     | Disallowed | Unlinked -> assert false
     | Created ->
       (* We'll bump [observing.num_on_update_handlers] when [t] is actually added to
          [observing.observers] at the start of the next stabilization. *)
       ()
     | In_use ->
       let observing = t.observing in
       observing.num_on_update_handlers <- observing.num_on_update_handlers + 1)
;;

let unlink_from_observing t =
  let prev = t.prev_in_observing in
  let next = t.next_in_observing in
  t.prev_in_observing <- Null;
  t.next_in_observing <- Null;
  if Or_null.is_this next then (Or_null.unsafe_value next).prev_in_observing <- prev;
  if Or_null.is_this prev then (Or_null.unsafe_value prev).next_in_observing <- next;
  let observing = t.observing in
  if phys_equal t (Or_null.value_exn observing.observers) then observing.observers <- next;
  observing.num_on_update_handlers
  <- observing.num_on_update_handlers - List.length t.on_update_handlers;
  t.on_update_handlers <- []
;;

let unlink_from_all t =
  let prev = t.prev_in_all in
  let next = t.next_in_all in
  t.prev_in_all <- Null;
  t.next_in_all <- Null;
  if Or_null.is_this next then Packed_.set_prev_in_all (Or_null.unsafe_value next) prev;
  if Or_null.is_this prev then Packed_.set_next_in_all (Or_null.unsafe_value prev) next
;;

let unlink t =
  unlink_from_observing t;
  unlink_from_all t
;;

module Packed = struct
  include Packed_

  let sexp_of_t (T internal_observer) =
    internal_observer |> [%sexp_of: _ internal_observer]
  ;;

  let invariant (T t) = invariant ignore t
end
