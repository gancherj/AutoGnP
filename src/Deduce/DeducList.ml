open MatData
open DeducMatSig

module ListD = MatDeduc (ListMat)
let solve_mat_list = ListD.solve_mat

let solve_other_list eis e = failwith "unimp"
