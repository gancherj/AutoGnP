
type id_var = int
type id_size = int
type vars = id_var list
type mon = {
    coeff : Num.num;
    vars : vars;
    length : int;
    size : id_size * id_size;
}

type pol = mon list

val mpoly_add : pol -> pol -> pol
val mpoly_mul : pol -> pol -> pol
val mpoly_sub : pol -> pol -> pol
val polys_mul : pol list -> pol

val deduce : pol -> pol list -> bool
val inverter : pol -> pol list -> pol
