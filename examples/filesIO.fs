module FileName
  type filename = string
  
  
module ACLs
  open FileName
  
  val canWrite : filename -> Tot bool
  let canWrite (f: filename) =
    match f with
    | "demo/tempfile" -> true
    | _ -> false
    
  val canRead : filename -> Tot bool
  let canRead (f: filename) =
    canWrite f || f = "demo/README"


module FileIO
  open ACLs
  open FileName
  assume val read : f:filename{canRead f} -> string
  assume val write : f:filename{canWrite f} -> string -> unit

  exception InvalidRead
  exception InvalidWrite
  
  val checkedRead : filename -> string
  let checkedRead f =
    if canRead f then read f else raise InvalidRead

  val checkedWrite : filename -> string -> unit
  let checkedWrite f s =
    if canWrite f then write f s else raise InvalidWrite

module UntrustedClientCode
  open FileIO
  open FileName
  
  let passwd = "demo/password"
  let readme = "demo/README"
  let tmp    = "demo/tempfile"
  
  let staticChacking () =
    read tmp    |> ignore;
    read readme |> ignore;
    write tmp "hello";
    
    (* read passwd |> ignore *) (* violates restrictions *)
    
    checkedRead tmp |> ignore;
    checkedRead passwd (* raises exception *)

