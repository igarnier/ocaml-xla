module Make (T : sig
  type elt

  val ty : elt Typed_xla.Type.t
end) =
struct
  type elt = T.elt
  type ('r, 'c) mat = ('r * 'c, elt) Typed_xla.t
  type 'a vec = ('a, elt) Typed_xla.t
  type 'a shape = 'a Typed_xla.shape

  type ('inputs, 'outputs) jacobian =
    { form : 'x. acc:('outputs, 'x) mat -> ('inputs, 'x) mat }

  (** [('args, 'ja_res, 'res_shape) internal_spec] is the internal type of node signatures.
    - The ['args] type parameter corresponds to the shape of inputs to the node.
    - The ['ja_res] type parameter corresponds to the shape of the family of jacobians
      of the node (one per input).
    - The ['res_shape] type parameter corresponds the shape of outputs of the node. *)
  type (_, _, _) internal_spec =
    | Returning : 'res shape -> (unit, unit, 'res) internal_spec
    | Argument :
        ('args, 'ja_res, 'res) internal_spec
        -> ('a vec * 'args, ('a, 'res) jacobian * 'ja_res, 'res) internal_spec

  let rec get_res_shape_from_internal_spec
    : type a b s. (a, b, s) internal_spec -> s shape
    =
   fun spec ->
    match spec with
    | Returning shape -> shape
    | Argument spec -> get_res_shape_from_internal_spec spec

  module Node = struct
    type _ accu =
      | Zero_accu
      | Some_accu : ('ret * 'a) mat -> 'ret vec accu

    (** ['s kernel] is the type of computations performed by a node. It specifies how to evaluate
      the computation forward and how to perform the backpropagation pass.
      The type parameter ['s] is the type of the kernel. *)
    type _ kernel =
      | Diff :
          { spec : ('args, 'ja_res, 'res_shape) internal_spec
          ; bwd : 'args node_vector
          ; forward : 'args -> 'res_shape vec
          ; jacobian : 'args -> 'ja_res
          }
          -> ('args -> 'res_shape vec) kernel
      | Cond :
          { cond : boolean t
          ; ift : 'a vec t
          ; iff : 'a vec t
          }
          -> (boolean * 'a vec * 'a vec -> 'a vec) kernel
      | Bool : boolean -> (unit -> boolean) kernel

    and ('args, 'ret) node =
      | Node :
          { id : int (** Unique id of the node. *)
          ; mutable fwd : opaque list
              (** List of nodes downstream of the node, i.e. nodes that receive the result of this node as input. *)
          ; mutable value : 'ret option (** Result of forward evaluation. *)
          ; mutable accu : 'ret accu (** Accumulator used in the backpropagation pass. *)
          ; kernel : ('args -> 'ret) kernel (** Kernel associated to the node. *)
          }
          -> ('args, 'ret) node

    and _ t =
      | Applied : ('args, 'ret vec) node -> 'ret vec t
      | Applied_bool : ('args, boolean) node -> boolean t

    and opaque = Opaque : 'ret t -> opaque

    and _ node_vector =
      | [] : unit node_vector
      | ( :: ) : 'a vec t * 'b node_vector -> ('a vec * 'b) node_vector

    (* TODO: why do we need both [spec] and [internal_spec]. *)
    type (_, _, _) spec =
      | Ret : 'res_shape C.shape -> (unit, unit, 'res_shape) spec
      | Arg :
          'a vec t * ('args, 'ja_res, 'res_shape) spec
          -> ('a vec * 'args, ('a, 'res_shape) jacobian * 'ja_res, 'res_shape) spec

    let return shape = Ret shape
    let ( @-> ) node spec = Arg (node, spec)

    let rec proj_backward : type a b c. (a, b, c) spec -> a node_vector = function
      | Ret _ -> []
      | Arg (node, rest) -> node :: proj_backward rest

    let rec proj_spec : type a b c. (a, b, c) spec -> (a, b, c) internal_spec = function
      | Ret shape -> Returning shape
      | Arg (_, rest) -> Argument (proj_spec rest)

    let fresh =
      let x = ref 0 in
      fun () ->
        let v = !x in
        incr x;
        v

    let rec iter_vec : type a. (opaque -> unit) -> a node_vector -> unit =
     fun f vec ->
      match vec with
      | [] -> ()
      | node :: tl ->
        f (Opaque node);
        iter_vec f tl

    let rec fold_vec : type a acc. (opaque -> acc -> acc) -> a node_vector -> acc -> acc =
     fun f vec acc ->
      match vec with
      | [] -> acc
      | node :: tl -> fold_vec f tl (f (Opaque node) acc)

    (* TODO Optim: do not store twice the same node in [fwd] *)
    let add_fwd : type a. a t -> opaque -> unit =
     fun node fwd ->
      match node with
      | Applied (Node node) -> node.fwd <- fwd :: node.fwd
      | Applied_bool (Node node) -> node.fwd <- fwd :: node.fwd

    let create_vec : type args ret. (args -> ret vec) kernel -> (args, ret vec) node =
     fun kernel ->
      let n = Node { id = fresh (); fwd = []; value = None; accu = Zero_accu; kernel } in
      let opaque_n = Opaque (Applied n) in
      (match kernel with
       | Diff payload -> iter_vec (fun (Opaque bwd) -> add_fwd bwd opaque_n) payload.bwd
       | Cond { cond; ift; iff } ->
         add_fwd cond opaque_n;
         add_fwd ift opaque_n;
         add_fwd iff opaque_n
         (* | Bool (C.B desc) -> (
          *     match desc with
          *     | C.True | C.False | C.Index_eq (_, _) | C.And (_, _) | C.Or (_, _) ->
          *         ()) *));
      n

    let create_bool
      : type args. (args -> boolean) kernel -> (args, boolean) node Promise.t
      =
     fun kernel ->
      let n = Node { id = fresh (); fwd = []; value = None; accu = Zero_accu; kernel } in
      (* No [add_fwd] required so far *)
      match kernel with
      | Bool expr ->
        let open Promise.Infix in
        let+ (C.B { desc; tag = _; hash = _ }) = expr in
        (match desc with
         | C.True | C.False | C.Index_eq (_, _) | C.And (_, _) | C.Or (_, _) -> n)

    let get_kernel (Node { kernel; _ }) = kernel

    let opaque_get_id (o : opaque) =
      let (Opaque an) = o in
      match an with
      | Applied (Node node) -> node.id
      | Applied_bool (Node node) -> node.id

    let opaque_get_fwd (o : opaque) =
      let (Opaque an) = o in
      match an with
      | Applied (Node node) -> node.fwd
      | Applied_bool (Node node) -> node.fwd

    let get_value_exn ~__LOC__ (Node node) = Helpers.opt_get ~__LOC__ node.value
    let set_value (Node node) v = node.value <- Some v
    let get_accu_opt (Node node) = node.accu
    let set_accu (Node node) v = node.accu <- Some_accu v

    let rec vec_get : type a. a node_vector -> a =
     fun vec ->
      match vec with
      | [] -> ()
      | Applied node :: tl ->
        let v = get_value_exn ~__LOC__ node in
        let r = vec_get tl in
        v, r

    let get_bwd : type a. a t -> opaque list =
     fun node ->
      match node with
      | Applied (Node node) ->
        (match node.kernel with
         | Diff { bwd; _ } -> fold_vec (fun opaque acc -> List.(opaque :: acc)) bwd []
         | Cond { cond; ift; iff } -> List.[ Opaque cond; Opaque ift; Opaque iff ])
      | Applied_bool (Node node) ->
        (match node.kernel with
         | Bool _ -> [])

    let rec refresh : opaque -> unit =
     fun (Opaque an) ->
      match an with
      | Applied node ->
        (match node with
         | Node { value = Some _; _ } -> ()
         | Node ({ value = None; kernel; _ } as payload) ->
           (match kernel with
            | Cond { cond; ift; iff } ->
              refresh (Opaque cond);
              refresh (Opaque ift);
              refresh (Opaque iff);
              let (Applied_bool cond) = cond in
              let (Applied ift) = ift in
              let (Applied iff) = iff in
              payload.value
                <- Some
                     (C.cond
                        (get_value_exn ~__LOC__ cond)
                        (get_value_exn ~__LOC__ ift)
                        (get_value_exn ~__LOC__ iff))
            | Diff { bwd; forward; _ } ->
              iter_vec (fun n -> refresh n) bwd;
              let nv = forward (vec_get bwd) in
              payload.value <- Some nv))
      | Applied_bool node ->
        (match node with
         | Node { value = Some _; _ } -> ()
         | Node ({ value = None; kernel; _ } as payload) ->
           (match kernel with
            | Bool b -> payload.value <- Some b))

    let get_value : type a. a t -> a =
     fun node ->
      refresh (Opaque node);
      match node with
      | Applied n -> get_value_exn ~__LOC__ n
      | Applied_bool n -> get_value_exn ~__LOC__ n

    let get_value_shape node = get_value node |> C.get_shape

    let rec get_res_shape : type a. a Core.vector Core.t t -> a C.shape =
     fun (Applied (Node node)) ->
      match node.kernel with
      | Cond { ift; _ } -> get_res_shape ift
      | Diff { spec; _ } -> get_res_shape_from_internal_spec spec

    let diff spec forward jacobian =
      create_vec
        (Diff { spec = proj_spec spec; bwd = proj_backward spec; forward; jacobian })

    let cond cond ift iff = create_vec (Cond { cond; ift; iff })
    let bool b = create_bool (Bool b)
    let applied node = Applied node
  end
end
