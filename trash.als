var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + File // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f]))
}

run example {}

pred directDelete [f: File] {
  f in File and not (f in Trash)
  after File' = File - f
  Trash' = Trash
}
 pred duplicate [f:File, fNew:File'] {
	f in File
	fNew not in File
	after File' = File + fNew
	Trash' = Trash
} 

pred restore [f : File] {
  // Only if 'f' is in Trash
  f in Trash

  // Remove 'f' from Trash in next step
  Trash' = Trash - f

  // File set remains the same
  File' = File
}
