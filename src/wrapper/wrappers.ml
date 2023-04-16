open! Base
open! Import
module CArray = Ctypes.CArray

let _add_compact =
  match Sys.getenv "OCAML_XLA_ADD_COMPACT" with
  | None | Some "false" | Some "0" -> false
  | Some _ -> true

module Status = struct
  let check_and_release status =
    if Ctypes.is_null status
    then Ok ()
    else (
      let error_message = W.Status.error_message status in
      W.Status.release status;
      Or_error.error_string error_message)

  let ok_exn status = check_and_release status |> Or_error.ok_exn
end

module Shape = struct
  type t = W.Shape.t

  (* This takes ownership of the pointer. *)
  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null Shape pointer";
    Caml.Gc.finalise W.Shape.release ptr;
    ptr

  let dimensions t =
    let dsize = W.Shape.dimensions_size t in
    List.init dsize ~f:(W.Shape.dimensions t)

  let element_type t = W.Shape.element_type t |> Element_type.of_c_int
end

module Builder = struct
  type t = W.Builder.t

  let create ~name =
    let ptr = W.Builder.create name in
    if Ctypes.is_null ptr then failwith "null Builder pointer";
    Caml.Gc.finalise W.Builder.release ptr;
    ptr

  let first_error t = W.Builder.first_error t |> Status.check_and_release
  let current_status t = W.Builder.get_current_status t |> Status.check_and_release
end

module Literal = struct
  type t = W.Literal.t

  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null Literal pointer";
    Caml.Gc.finalise W.Literal.release ptr;
    ptr

  let create element_type dims =
    let dims = List.map dims ~f:Int64.of_int |> CArray.of_list Ctypes.int64_t in
    let t =
      W.Literal.create_from_shape
        (Element_type.to_c_int element_type)
        (CArray.start dims)
        (CArray.length dims |> Unsigned.Size_t.of_int)
    in
    keep_alive dims;
    of_ptr t

  let clone t = W.Literal.clone t |> of_ptr

  let reshape t dims =
    let dims = List.map dims ~f:Int64.of_int |> CArray.of_list Ctypes.int64_t in
    let ptr = Ctypes.(allocate_n (ptr W.Literal.struct_) ~count:1) in
    let status =
      W.Literal.reshape
        t
        (CArray.start dims)
        (CArray.length dims |> Unsigned.Size_t.of_int)
        ptr
    in
    keep_alive dims;
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let convert t element_type =
    let ptr = Ctypes.(allocate_n (ptr W.Literal.struct_) ~count:1) in
    let status = W.Literal.convert t (Element_type.to_c_int element_type) ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let element_type t = W.Literal.element_type t |> Element_type.of_c_int
  let size_bytes t = W.Literal.size_bytes t |> Int64.to_int_exn
  let element_count t = W.Literal.element_count t |> Int64.to_int_exn

  let shape t =
    let ptr = Ctypes.(allocate_n (ptr W.Shape.struct_) ~count:1) in
    W.Literal.shape t ptr;
    Ctypes.( !@ ) ptr |> Shape.of_ptr
end

module Op = struct
  type t =
    { ptr : W.Op.t
    ; builder : Builder.t
    }

  let of_ptr ptr ~builder =
    if Ctypes.is_null ptr then failwith "null Op pointer";
    Caml.Gc.finalise W.Op.release ptr;
    { ptr; builder }

  let constant builder literal = W.Op.constant_literal builder literal |> of_ptr ~builder
  let add t1 t2 = W.Op.add t1.ptr t2.ptr |> of_ptr ~builder:t1.builder
end

module Computation = struct
  type t = W.Computation.t

  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null Computation pointer";
    Caml.Gc.finalise W.Computation.release ptr;
    ptr

  let name = W.Computation.name

  let build ~root =
    let ptr = Ctypes.(allocate_n (ptr W.Computation.struct_) ~count:1) in
    let status = W.Computation.build root.Op.builder root.ptr ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr
end

module PjRtClient0 = struct
  type t = W.PjRtClient.t

  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null PjRtlient pointer";
    Caml.Gc.finalise W.PjRtClient.release ptr;
    ptr
end

module PjRtDevice = struct
  (* The lifetime of a device pointer is tied to the client from which
     the device was extracted from. *)
  type t =
    { ptr : W.PjRtDevice.t
    ; client : PjRtClient0.t
    }

  let of_ptr ptr ~client = { ptr; client }
  let id t = W.PjRtDevice.id t.ptr
  let process_index t = W.PjRtDevice.process_index t.ptr
  let local_hardware_id t = W.PjRtDevice.local_hardware_id t.ptr
  let kind t = W.PjRtDevice.kind t.ptr
  let debug_string t = W.PjRtDevice.debug_string t.ptr
  let to_string t = W.PjRtDevice.to_string t.ptr
end

module PjRtClient = struct
  include PjRtClient0

  let cpu () =
    let ptr = Ctypes.(allocate_n (ptr W.PjRtClient.struct_) ~count:1) in
    let status = W.PjRtClient.cpu ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let gpu ~memory_fraction ~preallocate =
    let ptr = Ctypes.(allocate_n (ptr W.PjRtClient.struct_) ~count:1) in
    let status = W.PjRtClient.gpu ptr memory_fraction preallocate in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let device_count = W.PjRtClient.device_count
  let addressable_device_count = W.PjRtClient.addressable_device_count

  let devices t =
    let count = device_count t in
    let device_ptr = Ctypes.(allocate_n (ptr W.PjRtDevice.struct_) ~count) in
    W.PjRtClient.devices t device_ptr;
    List.init count ~f:(fun index ->
      Ctypes.(!@(device_ptr +@ index)) |> PjRtDevice.of_ptr ~client:t)

  let addressable_devices t =
    let count = addressable_device_count t in
    let device_ptr = Ctypes.(allocate_n (ptr W.PjRtDevice.struct_) ~count) in
    W.PjRtClient.addressable_devices t device_ptr;
    List.init count ~f:(fun index ->
      Ctypes.(!@(device_ptr +@ index)) |> PjRtDevice.of_ptr ~client:t)

  let platform_name = W.PjRtClient.platform_name
  let platform_version = W.PjRtClient.platform_version
end

module PjRtBuffer = struct
  type t = W.PjRtBuffer.t

  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null PjRtBuffer pointer";
    Caml.Gc.finalise W.PjRtBuffer.release ptr;
    ptr

  let of_host_literal literal ~device =
    let ptr = Ctypes.(allocate_n (ptr W.PjRtBuffer.struct_) ~count:1) in
    let status =
      W.PjRtBuffer.from_host_literal device.PjRtDevice.client device.ptr literal ptr
    in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let copy_to_device t ~device =
    let ptr = Ctypes.(allocate_n (ptr W.PjRtBuffer.struct_) ~count:1) in
    let status = W.PjRtBuffer.copy_to_device t device.PjRtDevice.ptr ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr

  let on_device_shape t = W.PjRtBuffer.on_device_shape t |> Shape.of_ptr

  let to_literal_sync t =
    let ptr = Ctypes.(allocate_n (ptr W.Literal.struct_) ~count:1) in
    let status = W.PjRtBuffer.to_literal_sync t ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> Literal.of_ptr
end

module PjRtLoadedExecutable = struct
  type t = W.PjRtLoadedExecutable.t

  let of_ptr ptr =
    if Ctypes.is_null ptr then failwith "null PjRtLoadedExecutable pointer";
    Caml.Gc.finalise W.PjRtLoadedExecutable.release ptr;
    ptr

  let compile client computation =
    let ptr = Ctypes.(allocate_n (ptr W.PjRtLoadedExecutable.struct_) ~count:1) in
    let status = W.PjRtLoadedExecutable.compile client computation ptr in
    Status.ok_exn status;
    Ctypes.( !@ ) ptr |> of_ptr
end
