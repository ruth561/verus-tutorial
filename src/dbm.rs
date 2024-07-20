use vstd::prelude::*;
use vstd::seq::*;

use crate::ext_int::*;


verus! {

struct Dbm {
    dimension: nat,
    matrix: Seq<Seq<ExtInt>>,
}

impl Dbm {

    spec fn idx(self, i: int) -> bool {
        &&& 0 <= i < self.dimension
    }

    spec fn idx2(self, i: int, j: int) -> bool {
        &&& 0 <= i < self.dimension
        &&& 0 <= j < self.dimension
    }

    spec fn idx3(self, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < self.dimension
        &&& 0 <= j < self.dimension
        &&& 0 <= k < self.dimension
    }

    spec fn triangle_inequality(self, i: int, j: int, k: int) -> bool {
        self.matrix[i][j] <= self.matrix[i][k] + self.matrix[k][j]
    }

    spec fn well_formed(self) -> bool {
        &&& 2 <= self.dimension
        &&& is_square_matrix(self.matrix, self.dimension)
        &&& forall|i:int| self.idx(i) ==> #[trigger] self.matrix[i][i].is_zero()
        &&& forall|i:int| self.idx(i) ==> #[trigger] self.matrix[i][0].is_non_negative()
        &&& forall|i:int| self.idx(i) ==> #[trigger] self.matrix[0][i].is_non_positive()
    }

    spec fn is_canonical(self) -> bool {
        &&& self.well_formed()
        &&& forall|i:int, j:int, k:int| self.idx3(i, j, k) ==> #[trigger] self.triangle_inequality(i, j, k)
    }

}

impl Dbm {

    // proof that the reset operation preserve the canonicity
    proof fn proof_reset(self, x: int, m: ExtInt) -> (result: Dbm)
        requires
            self.is_canonical(),
            1 <= x < self.dimension,
            m.is_non_negative(),
            m.is_int(),
        ensures
            result.matrix == spec_reset(self.matrix, self.dimension, x, m),
            result.is_canonical(),
    {
        let result = Dbm {
            dimension: self.dimension,
            matrix: spec_reset(self.matrix, self.dimension, x, m),
        };
        lem_reset(self.matrix, self.dimension, x, m);

        // needed to prove
        //   result.matrix[x][0].is_non_negative() and
        //   result.matrix[0][x].is_non_positive()
        // since
        //   result.matrix[x][0] == self.matrix[0][0] + m and 
        //   result.matrix[0][x] == self.matrix[0][0] - m
        assert(self.matrix[0][0].is_zero());

        assert forall|i:int, j:int, k:int| result.idx3(i, j, k) implies #[trigger] result.triangle_inequality(i, j, k) by {
            assert(result.matrix[x][x].is_zero());
            if        i == x && j == x && k == x {
                // proof by assert(self.matrix[0][0].is_zero())
            } else if i == x && j == x && k != x {
                // result.matrix[x][x] == self.matrix[0][0] <= self.matrix[0][k] + self.matrix[k][0]
                //   == (self.matrix[0][k] + m) + (self.matrix[k][0] - m) == result.matrix[x][k] + result.matrix[k][x]
                assert(self.triangle_inequality(0, 0, k));
            } else if i == x && j != x && k == x {
                // proof by assert(self.matrix[x][x].is_zero())
            } else if i == x && j != x && k != x {
                // result.matrix[x][j] == self.matrix[0][j] + m <= (self.matrix[0][k] + m) + self.matrix[k][j]
                //   == result.matrix[x][k] + result.matrix[k][j]
                assert(self.triangle_inequality(0, j, k));
            } else if i != x && j == x && k == x {
                // proof by assert(self.matrix[x][x].is_zero())
            } else if i != x && j == x && k != x {
                // same as above
                assert(self.triangle_inequality(i, 0, k));
            } else if i != x && j != x && k == x {
                // same as above
                assert(self.triangle_inequality(i, j, 0));
            } else {//i != x && j != x && k != x
                // no change
                assert(self.triangle_inequality(i, j, k));
            }
        };
        result
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
        1 <= x < n,
        is_square_matrix(matrix, n),
        m.is_non_negative(),
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
        1 <= x < n,
        is_square_matrix(matrix, n),
        m.is_non_negative(),
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
