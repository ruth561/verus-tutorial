use vstd::prelude::*;
use vstd::seq::*;

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

// resetの処理の前後におけるDBMの関係性を示す述語
// x行とx列の値が更新され、それ以外の値はd_oldのまま
// [[---, ???, ... , ---],
//  [???,   0, ... , ???],
//  [---, ???, ... , ---],
//    ...
//  [---, ???, ... , ---]]
// 単に行列の変換処理を表現したもの
spec fn spec_reset(matrix: Seq<Seq<ExtInt>>, n: nat, x: int, m: ExtInt) -> Seq<Seq<ExtInt>>
    recommends
        is_square_matrix(matrix, n),
        1 <= x < n,
        is_non_negative(m),
        m.is_int(),
{
    matrix.map(|i:int, seq:Seq<ExtInt>| {
        if i != x {
            seq.update(x, seq[0] - m)
        } else {
            matrix[0].map(|j:int, e:ExtInt|
                if j != x {
                    e + m
                } else {
                    matrix[x][x]
                }
            )
        }
    })
}

proof fn lem_reset(matrix: Seq<Seq<ExtInt>>, n: nat, x: int, m: ExtInt)
    requires
        is_square_matrix(matrix, n),
        1 <= x < n,
        is_non_negative(m),
        m.is_int(),
    ensures
        is_square_matrix(spec_reset(matrix, n, x, m), n),
        spec_reset(matrix, n, x, m)[x][x] == matrix[x][x],
        forall|i:int| 0 <= i < n && i != x ==> #[trigger] spec_reset(matrix, n, x, m)[x][i] == matrix[0][i] + m,
        forall|i:int| 0 <= i < n && i != x ==> #[trigger] spec_reset(matrix, n, x, m)[i][x] == matrix[i][0] - m,
        forall|i:int, j:int|
            0 <= i < n && i != x &&
            0 <= j < n && j != x ==>
            #[trigger] spec_reset(matrix, n, x, m)[i][j] == matrix[i][j],
{
    let result = spec_reset(matrix, n, x, m);
    assert forall|i:int, j:int|
        0 <= i < n && i != x &&
        0 <= j < n && j != x implies
        result[i][j] == matrix[i][j] by
    {
        assert(len_is_n(matrix[i], n));
        axiom_seq_update_different(matrix[i], j, x, matrix[i][0] - m);
    };

    assert(len_is_n(matrix[0], n));
    assert(result[x][x] == matrix[x][x]);
    assert(forall|i:int| #![auto] 0 <= i < n && i != x ==>     result[x][i] == matrix[0][i] + m);
    assert forall|i:int| #![auto] 0 <= i < n && i != x implies result[i][x] == matrix[i][0] - m by {
        assert(len_is_n(matrix[i], n));
        axiom_seq_update_same(matrix[i], x, matrix[i][0] - m);
    }

    // is_square_matrix(result, n)
    assert forall|i:int| 0 <= i < n implies #[trigger] len_is_n(result[i], n) by {
        assert(len_is_n(matrix[i], n));
    }
}

} // verus!
