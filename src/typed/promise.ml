type 'a t = { mutable state : 'a state }

and 'a state =
  | Resolved of 'a
  | Pending of
      { root : bool
      ; pending : 'a pending
      }
  | Proxy of 'a t

and 'a pending = { mutable callbacks : ('a -> unit) list }

let underlying : type a. a t -> a t =
  let rec loop (p : a t) (acc : a t list) =
    match p.state with
    | Proxy p' -> loop p' (p :: acc)
    | Resolved _ | Pending _ ->
      List.iter
        (fun p' ->
          assert (not (p' == p));
          p'.state <- Proxy p)
        acc;
      p
  in
  fun p -> loop p []

let peek p =
  match (underlying p).state with
  | Resolved v -> `Resolved v
  | Pending p -> if p.root then `Pending_root else `Pending_internal
  | Proxy _ -> assert false

let resolve p v =
  let p = underlying p in
  match p.state with
  | Resolved _ -> failwith "already resolved"
  | Pending { pending; _ } ->
    p.state <- Resolved v;
    List.iter (fun r -> r v) pending.callbacks
  | Proxy _ -> assert false

let is_resolved p =
  match peek p with
  | `Resolved v -> Some v
  | `Pending_root | `Pending_internal -> None

(* Expected behaviour: make [p] behave as [of_] when it makes sense,
   fail otherwise *)
let make_proxy ~of_ p =
  let p = underlying p in
  let of_ = underlying of_ in
  match p.state with
  | Resolved _ -> invalid_arg "make_proxy: already resolved"
  | Pending { root; pending } ->
    if root
    then (
      match of_.state with
      | Resolved v -> resolve p v
      | Pending { pending = of_pending; _ } ->
        of_pending.callbacks <- List.rev_append pending.callbacks of_pending.callbacks;
        p.state <- Proxy of_
      | Proxy _ -> assert false)
    else invalid_arg "make_proxy:"
  | Proxy _ -> assert false

let return x = { state = Resolved x }

let unknown () =
  let pending = { callbacks = [] } in
  let state = Pending { pending; root = true } in
  let promise = { state } in
  promise, resolve promise

let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
  let m = underlying m in
  match m.state with
  | Proxy _ ->
    (* Can't be a proxy b-c of [underlying] *)
    assert false
  | Resolved v -> f v
  | Pending { pending; _ } ->
    let bind_pending = { callbacks = [] } in
    let bind_promise = { state = Pending { pending = bind_pending; root = false } } in
    let bind_resolver v =
      let p = f v |> underlying in
      match p.state with
      | Proxy _ ->
        (* Can't be a proxy b-c of [underlying] *)
        assert false
      | Resolved v ->
        List.iter (fun r -> r v) bind_pending.callbacks;
        bind_promise.state <- Resolved v
      | Pending { pending = p_pending; _ } ->
        p_pending.callbacks <- List.rev_append bind_pending.callbacks p_pending.callbacks;
        bind_promise.state <- Proxy p
    in
    pending.callbacks <- bind_resolver :: pending.callbacks;
    bind_promise

let map f m =
  let m = underlying m in
  match m.state with
  | Proxy _ ->
    (* Can't be a proxy b-c of [underlying] *)
    assert false
  | Resolved x -> return (f x)
  | Pending { pending; _ } ->
    let map_pending = { callbacks = [] } in
    let map_promise = { state = Pending { pending = map_pending; root = false } } in
    let map_resolver v =
      let v = f v in
      map_promise.state <- Resolved v;
      List.iter (fun r -> r v) map_pending.callbacks
    in
    pending.callbacks <- map_resolver :: pending.callbacks;
    map_promise

let map2 f p1 p2 =
  let p1 = underlying p1 in
  let p2 = underlying p2 in
  match p1.state, p2.state with
  | Proxy _, _ | _, Proxy _ ->
    (* Can't be a proxy b-c of [underlying] *)
    assert false
  | Resolved x, Resolved y -> return (f x y)
  | Pending _, Resolved y -> map (fun x -> f x y) p1
  | Resolved x, Pending _ -> map (fun y -> f x y) p2
  | Pending { pending = p1; _ }, Pending { pending = p2; _ } ->
    let map2_pending = { callbacks = [] } in
    let map2_promise = { state = Pending { pending = map2_pending; root = false } } in
    let left = ref None in
    let right = ref None in
    let map2_resolver storage v =
      storage := Some v;
      match !left, !right with
      | None, _ | _, None -> ()
      | Some x, Some y ->
        let v = f x y in
        map2_promise.state <- Resolved v;
        List.iter (fun r -> r v) map2_pending.callbacks
    in
    p1.callbacks <- map2_resolver left :: p1.callbacks;
    p2.callbacks <- map2_resolver right :: p2.callbacks;
    map2_promise

let run p =
  match peek p with
  | `Resolved v -> v
  | `Pending_root | `Pending_internal -> failwith "Promise.run: unresolved promise"

module Infix = struct
  let return = return
  let ( let* ) = bind
  let ( let+ ) m f = map f m
  let ( and+ ) m1 m2 = map2 (fun x y -> x, y) m1 m2
end
