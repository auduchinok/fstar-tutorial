module RefTest
  val newCounter : int -> (unit -> int)
  let newCounter init =
    let c = ref init in
    fun () -> c := !c + 1; !c
