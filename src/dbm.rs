use vstd::prelude::*;

use crate::ext_int::*;


verus! {

struct Dbm {
    dimension: nat,
    matrix: Seq<Seq<ExtInt>>,
}

impl Dbm {

    spec fn is_consistent(self) -> bool {
        &&& is_square_matrix(self.matrix, self.dimension)
        &&& forall|i:int| 0 <= i < self.dimension ==> #[trigger] is_zero(self.matrix[i][i])
        &&& forall|i:int| 0 <= i < self.dimension ==> #[trigger] is_non_negative(self.matrix[i][0])
    }

    spec fn is_canonical(self) -> bool {
        &&& self.is_consistent()
        &&& forall|i:int, j:int, k:int|
            0 <= i < self.dimension &&
            0 <= j < self.dimension &&
            0 <= k < self.dimension ==>
            #[trigger] triangle_inequality(self.matrix, i, j, k)
    }

}

// 引数で受け取った行列がn×nの正方行列であるか？
spec fn is_square_matrix<T>(matrix: Seq<Seq<T>>, n: nat) -> bool {
    &&& len_is_n(matrix, n)
    &&& forall|i:int| 0 <= i < n ==> #[trigger] len_is_n(matrix[i], n)
}

spec fn len_is_n<T>(seq: Seq<T>, n: nat) -> bool {
    seq.len() == n
}

spec fn is_zero(ei: ExtInt) -> bool {
    ei == ExtInt::Int(0)
}

spec fn is_non_negative(ei: ExtInt) -> bool {
    ||| ei.is_inf()
    ||| ei.is_int() && 0 <= ei.unwrap()
}

spec fn is_non_positive(ei: ExtInt) -> bool {
    ei.is_int() && 0 >= ei.unwrap()
}

spec fn triangle_inequality(matrix: Seq<Seq<ExtInt>>, i: int, j: int, k: int) -> bool {
    matrix[i][j] <= matrix[i][k] + matrix[k][j]
}

} // verus!
