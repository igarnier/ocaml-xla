include (
  struct
    open Bigarray

    let element_type_of_kind (type a b) (k : (a, b) kind) =
      let open Xla.Element_type in
      match k with
      | Float32 -> F32
      | Float64 -> F64
      | Int8_signed -> S8
      | Int8_unsigned -> U8
      | Int16_signed -> S16
      | Int16_unsigned -> U16
      | Int32 -> S32
      | Int64 -> S64
      | Int -> assert false
      | Nativeint -> assert false
      | Complex32 -> assert false
      | Complex64 -> C64
      | Char -> U8

    module Type = struct
      type f32 = float32_elt = Float32_elt
      type f64 = float64_elt = Float64_elt
      type 'a t = E : ('a, 'b) kind -> 'b t

      let f32 : f32 t = E Float32
      let f64 = E Float64
      let to_xla : type a. a t -> Xla.Element_type.t = fun (E k) -> element_type_of_kind k
    end

    module Arr = struct
      type 'a t = BA : ('a, 'b, c_layout) Genarray.t -> 'b t

      let dims (BA arr) = Genarray.dims arr
      let to_xla (BA arr) = Xla.Literal.of_bigarray arr
      let of_xla lit (Type.E kind) = BA (Xla.Literal.to_bigarray lit ~kind)

      let of_array_f32 arr : _ t =
        BA (genarray_of_array1 (Array1.of_array Float32 c_layout arr))

      let of_array_f64 arr =
        BA (genarray_of_array1 (Array1.of_array Float64 c_layout arr))

      let elt_type (BA arr) =
        let k = Genarray.kind arr in
        Type.E k
    end
  end :
    sig
      module Type : sig
        type f32
        type f64
        type _ t

        val f32 : f32 t
        val f64 : f64 t
        val to_xla : 'a t -> Xla.Element_type.t
      end

      module Arr : sig
        type _ t

        val dims : _ t -> int array
        val to_xla : 'a t -> Xla.Literal.t
        val of_xla : Xla.Literal.t -> 'a Type.t -> 'a t
        val of_array_f32 : float array -> Type.f32 t
        val of_array_f64 : float array -> Type.f64 t
        val elt_type : 'a t -> 'a Type.t
      end
    end)

type scalar = Scalar_tag
type index = Index_tag
type double_ba = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Genarray.t

type _ shape_desc =
  | Scalar : scalar shape_desc (* Scalar (isomorphic to Dim 1) *)
  | Dim : int -> index shape_desc (* One-dimensional shape (Array) *)
  | Tensor : 'a shape * 'b shape -> ('a * 'b) shape_desc (* Tensor of shapes *)

and 'a shape = 'a shape_desc Promise.t

type ('sh, 'elt) t =
  { shape : 'sh shape
  ; desc : ('sh, 'elt) desc
  }

and (_, _) desc =
  | Binop : ('a, 'b, 'c) binop * ('a, 'elt) t * ('b, 'elt) t -> ('c, 'elt) desc
  | Literal : 'elt Arr.t -> ('a, 'elt) desc
  | Parameter :
      { name : string
      ; id : int
      ; elt_ty : 'elt Type.t
      }
      -> ('a, 'elt) desc

and (_, _, _) binop =
  | Add : ('a, 'a, 'a) binop
  | Sub : ('a, 'a, 'a) binop
  | Mul : ('a, 'a, 'a) binop
  | Div : ('a, 'a, 'a) binop
  | Matmul : ('a * 'b, 'c * 'a, 'c * 'b) binop
  | Dot : ('a, 'a, scalar) binop

type ('sh, 'elt) literal =
  { shape : 'sh shape
  ; elt_ty : 'elt Type.t
  ; lit : 'elt Arr.t
  }

type ('sh, 'elt) arg =
  { name : string
  ; shape : 'sh shape
  ; elt_ty : 'elt Type.t
  }

type (_, _) prototype =
  | Returning :
      { shape : 'sh shape
      ; elt_ty : 'elt Type.t
      }
      -> (('sh, 'elt) t, ('sh, 'elt) t) prototype
  | Arg :
      ('sh, 'elt) arg * ('args, 'ret) prototype
      -> (('sh, 'elt) t -> 'args, 'ret) prototype

type (_, _) arguments =
  | [] : ('a, 'a) arguments
  | ( :: ) :
      ('sh, 'elt) literal * ('args, 'ret) arguments
      -> (('sh, 'elt) t -> 'args, 'ret) arguments

type (_, _) program =
  | Program :
      { prototype : ('p, ('sh, 'elt) t) prototype
      ; code : 'p
      }
      -> ('p, ('sh, 'elt) t) program

(** Shape handling *)

module Shape = struct
  exception Join_error : 'a shape * 'b shape -> exn

  let make desc : _ shape = Promise.return desc
  let scalar = make Scalar
  let tensor l r = make (Tensor (l, r))

  let rank_one len =
    if len <= 0 then invalid_arg "rank_one: dimension must be > 0";
    make (Dim len)

  let unknown () =
    let p, _resolver = Promise.unknown () in
    p

  let create ?shape () : 'a shape =
    match shape with
    | None -> unknown ()
    | Some d -> make d

  let rec join : type a. ?__LOC__:string -> a shape -> a shape -> unit =
   fun ?(__LOC__ = "?") sx sy ->
    match Promise.peek sx, Promise.peek sy with
    | `Pending_internal, _ | _, `Pending_internal -> assert false
    | `Pending_root, `Pending_root -> Promise.make_proxy ~of_:sx sy
    | `Pending_root, `Resolved _ -> Promise.make_proxy ~of_:sy sx
    | `Resolved _, `Pending_root -> Promise.make_proxy ~of_:sx sy
    | `Resolved desc1, `Resolved desc2 ->
      (match desc1, desc2 with
       | Scalar, Scalar -> ()
       | Dim i, Dim j -> if i = j then () else raise (Join_error (sx, sy))
       | Tensor (l1, r1), Tensor (l2, r2) ->
         join l1 l2;
         join r1 r2)

  let rec numel : type a. a shape -> int Promise.t =
   fun shape ->
    let open Promise.Infix in
    let* desc = shape in
    match desc with
    | Scalar -> return 1
    | Dim i -> return i
    | Tensor (l, r) ->
      let* l = numel l in
      let* r = numel r in
      return (l * r)

  let rec singleton : type a. a shape -> a shape =
   fun shape ->
    let open Promise.Infix in
    let* desc = shape in
    match desc with
    | Scalar -> (return Scalar : a shape)
    | Dim _i -> (return (Dim 1) : a shape)
    | Tensor (l, r) ->
      let l = singleton l in
      let r = singleton r in
      return (Tensor (l, r))

  let rec equal : type a b. a shape -> b shape -> (a, b) Refl.eq option Promise.t =
   fun shape1 shape2 ->
    let open Promise.Infix in
    let* desc1 = shape1 in
    let* desc2 = shape2 in
    match desc1, desc2 with
    | Dim i1, Dim i2 ->
      if Int.equal i1 i2 then return (Some (Refl.Refl : (a, b) Refl.eq)) else return None
    | Tensor (l1, r1), Tensor (l2, r2) ->
      let* eq1 = equal l1 l2 in
      let* eq2 = equal r1 r2 in
      (match eq1, eq2 with
       | None, _ | _, None -> return None
       | Some Refl, Some Refl -> return (Some (Refl.Refl : (a, b) Refl.eq)))
    | _ -> return None

  let rec hash : type a. a shape -> int Promise.t =
   fun shape ->
    let open Promise.Infix in
    let* desc = shape in
    match desc with
    | Scalar -> return @@ Hashtbl.hash ()
    | Dim i -> return @@ Hashtbl.hash i
    | Tensor (l, r) ->
      let* lh = hash l in
      let* rh = hash r in
      return @@ Hashtbl.hash (lh, rh)

  let rec is_ground : type a. a shape -> bool =
   fun shape ->
    let desc_opt = Promise.is_resolved @@ shape in
    match desc_opt with
    | None -> false
    | Some desc ->
      (match desc with
       | Scalar | Dim _ -> true
       | Tensor (l, r) -> is_ground l && is_ground r)

  let rec flatten : type a. a shape -> int list Promise.t =
   fun shape ->
    let open Promise.Infix in
    let* desc = shape in
    match desc with
    | Scalar -> return ([ 1 ] : int list)
    | Dim i -> return ([ i ] : int list)
    | Tensor (ls, rs) ->
      let* l = flatten ls in
      let* r = flatten rs in
      return (l @ r)
end

(** Helpers *)

let get_shape : type a elt. (a, elt) t -> a shape = fun e -> e.shape

exception
  Shape_error of
    { loc : string option
    ; msg : string
    }

let shape_error ?__LOC__ msg = raise (Shape_error { loc = __LOC__; msg })

let assert_shape
  :  ?__LOC__:string -> 'a shape -> ('a shape -> (unit, string) Result.t Promise.t)
  -> 'a shape
  =
 fun ?__LOC__ shape pred ->
  let open Promise.Infix in
  let* res = pred shape in
  match res with
  | Ok () -> shape
  | Error msg -> shape_error ?__LOC__ msg

let gen =
  let x = ref 0 in
  fun () ->
    let v = !x in
    incr x;
    v

let gen_name =
  let x = ref 0 in
  fun () ->
    let v = !x in
    incr x;
    Format.asprintf "arg%d" v

let make shape desc = { shape; desc }

let check_bigarray_matches_shape shape ba =
  let open Promise.Infix in
  let+ ba_shape = Shape.flatten shape |> Promise.map Array.of_list in
  let dims = Arr.dims ba in
  let ba_shape_len = Array.length ba_shape in
  let dims_len = Array.length dims in
  if ba_shape_len = dims_len
  then if Array.for_all2 Int.equal ba_shape dims then Result.ok () else Error ba_shape
  else Error ba_shape

let lit ?shape lit =
  let shape =
    match shape with
    | None -> Shape.unknown ()
    | Some sh -> sh
  in
  { shape; elt_ty = Arr.elt_type lit; lit }

let arg ?name ?shape elt_ty =
  let shape =
    match shape with
    | None -> Shape.unknown ()
    | Some sh -> sh
  in
  let name =
    match name with
    | None -> gen_name ()
    | Some name -> name
  in
  { shape; elt_ty; name }

let program prototype code = Program { prototype; code }

(** Printers *)

let rec pp_shape : type a. Format.formatter -> a shape -> unit =
 fun fmtr shape ->
  let open Format in
  let desc_state = shape |> Promise.is_resolved in
  match desc_state with
  | None -> fprintf fmtr "?"
  | Some desc -> pp_shape_desc fmtr desc

and pp_shape_desc : type a. Format.formatter -> a shape_desc -> unit =
 fun fmtr (shape : a shape_desc) ->
  match shape with
  | Scalar -> Format.fprintf fmtr "()"
  | Dim i -> Format.fprintf fmtr "%d" i
  | Tensor (l, r) -> Format.fprintf fmtr "[ %a %a ]" pp_shape l pp_shape r

let pp_bigarray_shape : Format.formatter -> int array -> unit =
 fun fmtr ba_shape ->
  let ba_shape = Array.to_list ba_shape in
  Format.pp_print_list
    ~pp_sep:(fun fmtr () -> Format.fprintf fmtr " ")
    Format.pp_print_int
    fmtr
    ba_shape

(** Constructors *)

let shape_constraints
  (type a b c elt)
  ~__LOC__
  (op : (a, b, c) binop)
  (x : (a, elt) t)
  (y : (b, elt) t)
  : c shape
  =
  match op with
  | Add ->
    let xs = get_shape x in
    let ys = get_shape y in
    Shape.join ~__LOC__ xs ys;
    xs
  | Sub ->
    let xs = get_shape x in
    let ys = get_shape y in
    Shape.join ~__LOC__ xs ys;
    xs
  | Mul ->
    let xs = get_shape x in
    let ys = get_shape y in
    Shape.join ~__LOC__ xs ys;
    xs
  | Div ->
    let xs = get_shape x in
    let ys = get_shape y in
    Shape.join ~__LOC__ xs ys;
    xs
  | Matmul ->
    let x_shape = get_shape x in
    let y_shape = get_shape y in
    let input_shape = Shape.create () in
    let mid_shape = Shape.create () in
    let output_shape = Shape.create () in
    Shape.join ~__LOC__ y_shape (Shape.tensor input_shape mid_shape);
    Shape.join ~__LOC__ x_shape (Shape.tensor mid_shape output_shape);
    Shape.tensor input_shape output_shape
  | Dot ->
    let xs = get_shape x in
    let ys = get_shape y in
    Shape.join ~__LOC__ xs ys;
    Shape.scalar

let binop ~__LOC__ op x y = make (shape_constraints ~__LOC__ op x y) (Binop (op, x, y))
let add x y = binop ~__LOC__ Add x y
let sub x y = binop ~__LOC__ Sub x y
let mul x y = binop ~__LOC__ Mul x y
let div x y = binop ~__LOC__ Div x y
let mm x y = binop ~__LOC__ Matmul x y
let dot x y = binop ~__LOC__ Dot x y

let arr shape ba =
  let checked_shape =
    assert_shape ~__LOC__ shape
    @@ fun shape ->
    let open Promise.Infix in
    let+ res = check_bigarray_matches_shape shape ba in
    Result.map_error
      (fun ba_shape ->
        Format.asprintf
          "Array shape %a does not match prescribed shape %a"
          pp_shape
          shape
          pp_bigarray_shape
          ba_shape)
      res
  in
  make checked_shape (Literal ba)

let returning ?shape elt_ty =
  let shape =
    match shape with
    | None -> Shape.unknown ()
    | Some sh -> sh
  in
  Returning { shape; elt_ty }

let ( @-> ) arg rest = Arg (arg, rest)

(** Interpretation in XLA language *)

let rec to_xla : type a elt. (a, elt) t -> Xla.Wrappers.Builder.t -> Xla.Op.t Promise.t =
 fun expr builder ->
  let open Promise.Infix in
  match expr.desc with
  | Binop (op, l, r) ->
    let+ l = to_xla l builder
    and+ r = to_xla r builder in
    (match op with
     | Add -> Xla.Op.add l r
     | Sub -> Xla.Op.sub l r
     | Mul -> Xla.Op.mul l r
     | Div -> Xla.Op.div l r
     | Matmul -> Xla.Op.matmul l r
     | Dot -> Xla.Op.dot l r)
  | Literal arr ->
    let lit = Arr.to_xla arr in
    Xla.Op.constant lit ~builder |> return
  | Parameter { name; id; elt_ty } ->
    let+ dims = Shape.flatten (get_shape expr) in
    let dims = Array.of_list dims in
    Xla.Op.parameter name ~id ~ty:(Type.to_xla elt_ty) ~dims ~builder

let apply_parameters : type proto ret. (proto, ret) program -> ret =
  let rec loop : type proto ret. (proto, ret) prototype -> proto -> ret =
   fun proto k ->
    match proto with
    | Returning _ -> k
    | Arg ({ name; shape; elt_ty }, rest) ->
      let id = gen () in
      let parameter = { shape; desc = Parameter { name; id; elt_ty } } in
      loop rest (k parameter)
  in
  fun (Program { prototype; code }) -> loop prototype code

let get_literal_vec : type proto ret. (proto, ret) arguments -> Xla.Literal.t array =
  let rec loop : type proto ret. (proto, ret) arguments -> Xla.Literal.t list =
   fun args ->
    match args with
    | [] -> ([] : _ list)
    | { shape = _; elt_ty = _; lit } :: rest ->
      let lit = Arr.to_xla lit in
      lit :: loop rest
  in
  fun args -> Array.of_list (loop args)

let rec get_returned_element_type
  : type proto sh elt. (proto, (sh, elt) t) prototype -> sh shape * elt Type.t
  =
 fun proto ->
  match proto with
  | Returning { elt_ty; shape } -> shape, elt_ty
  | Arg (_, rest) -> get_returned_element_type rest

let rec unify_prototype_and_arguments_shapes
  : type proto sh elt.
    (proto, (sh, elt) t) prototype -> (proto, (sh, elt) t) arguments -> unit
  =
 fun proto args ->
  match proto, args with
  | Returning _, [] -> ()
  | Arg (arg, rest), arg_proto :: arg_rest ->
    Shape.join ~__LOC__ arg.shape arg_proto.shape;
    unify_prototype_and_arguments_shapes rest arg_rest

let test =
  program (arg Type.f32 @-> arg Type.f32 @-> returning Type.f32)
  @@ fun lol foo ->
  add
    (add lol foo)
    (arr Shape.(tensor (rank_one 2) (rank_one 2)) (Arr.of_array_f32 [| 1.0 |]))

let exec
  : type proto sh elt.
    (proto, (sh, elt) t) program -> (proto, (sh, elt) t) arguments -> (sh, elt) literal
  =
 fun (Program { prototype; _ } as program) args ->
  let cpu = Xla.Client.cpu () in
  let builder = Xla.Builder.create ~name:"mybuilder" in
  let body = apply_parameters program in
  let root_p = to_xla body builder in
  let literals = get_literal_vec args in
  let shape, elt_ty = get_returned_element_type prototype in
  Shape.join ~__LOC__ shape (get_shape body);
  unify_prototype_and_arguments_shapes prototype args;
  match Promise.peek root_p with
  | `Pending_internal | `Pending_root ->
    Format.kasprintf
      failwith
      "eval: the program has some unbound shape, please resolve all shape variables"
  | `Resolved root ->
    let computation = Xla.Computation.build ~root in
    let exe = Xla.Executable.compile cpu computation in
    let buffers = Xla.Executable.execute exe literals in
    let literal = Xla.Buffer.to_literal_sync buffers.(0).(0) in
    { shape; elt_ty; lit = Arr.of_xla literal elt_ty }
