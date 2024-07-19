use vstd::prelude::*;
use vstd::seq::*;

use crate::ext_i64::*;


verus! {

struct Dbm {
    dimension: nat,
    matrix: Seq<Seq<ExtI64>>,
}

impl Dbm {

    spec fn is_consistent(self) -> bool {
        &&& 2 <= self.dimension
        &&& is_square_matrix(self.matrix, self.dimension)
        &&& forall|i:int| 0 <= i < self.dimension ==> #[trigger] is_zero(self.matrix[i][i])
        &&& forall|i:int| 0 <= i < self.dimension ==> #[trigger] is_non_negative(self.matrix[i][0])
        &&& forall|i:int| 0 <= i < self.dimension ==> #[trigger] is_non_positive(self.matrix[0][i])
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

impl Dbm {
    proof fn proof_reset(self, x: int, m: ExtI64) -> (result: Dbm)
        requires
            self.is_canonical(),
            1 <= x < self.dimension,
            is_non_negative(m),
            m.is_int(),
        // ensures
        //     result.is_canonical(),
    {
        let result = Dbm {
            dimension: self.dimension,
            matrix: spec_reset(self.matrix, self.dimension, x, m),
        };
        lem_reset(self.matrix, self.dimension, x, m);

        // assert(is_square_matrix(result.matrix, result.dimension));
        // assert(forall|i:int| 0 <= i < result.dimension ==> #[trigger] is_zero(result.matrix[i][i]));
        assert(is_zero(self.matrix[0][0])); // needed for proof is_non_negative(result.matrix[x][0])
        // assert(forall|i:int| 0 <= i < result.dimension ==> #[trigger] is_non_negative(result.matrix[i][0]));
        assert(result.is_consistent());

        assert(is_square_matrix(self.matrix, self.dimension));
        assert(is_square_matrix(result.matrix, result.dimension));
        assert(2 <= self.matrix.len());

        assert forall|i:int, j:int, k:int|
            0 <= i < result.dimension &&
            0 <= j < result.dimension &&
            0 <= k < result.dimension implies
            #[trigger] triangle_inequality(result.matrix, i, j, k) by
        {
            assert(len_is_n(result.matrix[0], result.dimension));
            assert(len_is_n(result.matrix[x], result.dimension));
            assert(is_zero(result.matrix[x][x]));
            if        i == x && j == x && k == x {
                assert(is_zero(result.matrix[x][x]));
            } else if i == x && j == x && k != x {
                // result.matrix[x][x] == self.matrix[0][0] <= self.matrix[0][k] + self.matrix[k][0] ==
                //     (self.matrix[0][k] + m) + (self.matrix[k][0] - m) == result.matrix[x][k] + result.matrix[k][x]
                assert(is_non_positive(self.matrix[0][k])); // precondition for non-overflow `self.matrix[0][k] + m`
                assert(result.matrix[x][k] == self.matrix[0][k] + m);
                assert(is_non_negative(self.matrix[k][0])); // precondition for non-overflow `self.matrix[k][0] - m`
                assert(result.matrix[k][x] == self.matrix[k][0] - m);
                assert(self.matrix[0][k] + self.matrix[k][0] == (self.matrix[0][k] + m) + (self.matrix[k][0] - m));
                assert(result.matrix[x][k] + result.matrix[k][x] == self.matrix[0][k] + self.matrix[k][0]);
                assert(triangle_inequality(self.matrix, 0, 0, k));
                assert(result.matrix[x][x] <= result.matrix[x][k] + result.matrix[k][x]);
            } else if i == x && j != x && k == x {
            } else if i == x && j != x && k != x {
                // result.matrix[x][j] == self.matrix[0][j] + m <= (self.matrix[0][k] + m) + self.matrix[k][j] == result.matrix[x][k] + result.matrix[k][j]
                // assert(is_non_positive(self.matrix[0][k])); // precondition for non-overflow `self.matrix[0][k] + m`
                // assert(result.matrix[x][k] == self.matrix[0][k] + m);
                // assert(is_non_positive(self.matrix[0][j])); // precondition for non-overflow `self.matrix[0][k] + m`
                // assert(result.matrix[x][j] == self.matrix[0][j] + m);
                // assert(triangle_inequality(self.matrix, 0, j, k));
                // assert(len_is_n(self.matrix[k], self.dimension));
                // assert(self.matrix[0][j] + m <= (self.matrix[0][k] + self.matrix[k][j]) + m);
                // assert(self.matrix[0][j] + m <= (self.matrix[0][k] + m) + self.matrix[k][j]);

                assume(false);
            }

            else {
                assume(false);
            }
        };
        assert(result.is_canonical());

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

spec fn is_zero(ei: ExtI64) -> bool {
    ei == ExtI64::Int(0)
}

spec fn is_non_negative(ei: ExtI64) -> bool {
    ||| ei.is_inf()
    ||| ei.is_int() && 0 <= ei.unwrap()
}

spec fn is_non_positive(ei: ExtI64) -> bool {
    ei.is_int() && 0 >= ei.unwrap()
}

// 非負を足したら、結果が小さくなることはない。
proof fn lem_add_non_negative(e1: ExtI64, e2: ExtI64)
    requires
        !e1.check_add_overflow(e2),
        is_non_negative(e2),
    ensures
        e1 <= e1 + e2,
{}

// #[verifier::external_body]
proof fn lem_add_plus_minus(e1: ExtI64, e2: ExtI64, m: ExtI64)
    requires
        !e1.check_add_overflow(e2),
        !e1.check_add_overflow(m),
        !e2.check_sub_overflow(m),
    ensures
        e1 + e2 == (e1 + m) + (e2 - m)
{
    // assert(m.is_int()); // from !e2.check_sub_overflow(m)
}

proof fn lem_assoc(e1: ExtI64, e2: ExtI64, e3: ExtI64)
    requires
        !e1.check_add_overflow(e2),
        !e2.check_add_overflow(e3),
        // !(e1 + e2).check_add_overflow(e3),
        // !(e1 + e2).check_add_overflow(e3),
    ensures
        (e1 + e2) + e3 == e1 + (e2 + e3),
{
    match (e1, e2, e3) {
        (ExtI64::Inf, _, _) => (),
        (_, ExtI64::Inf, _) => (),
        (_, _, ExtI64::Inf) => (),
        (ExtI64::Int(n1), ExtI64::Int(n2), ExtI64::Int(n3)) => {
            // assert((n1 + n2) as i64 + n3 == n1 + (n2 + n3) as i64);
            // assert(e1 + e2 == ExtI64::Int((n1 + n2) as i64));
            // assert((e1 + e2) + e3 == ExtI64::Int(((n1 + n2) as i64 + n3) as i64));

            // assert(e1 + e2 == ExtI64::Int((n1 + n2) as i64));
            // assert((e1 + e2) + e3 == ExtI64::Int(((n1 + n2) as i64 + n3) as i64));

            // assert(e2 + e3 == ExtI64::Int((n2 + n3) as i64));
            // assert(e1 + (e2 + e3) == ExtI64::Int((n1 + (n2 + n3) as i64) as i64));
        },
    }
}

spec fn triangle_inequality(matrix: Seq<Seq<ExtI64>>, i: int, j: int, k: int) -> bool {
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
spec fn spec_reset(matrix: Seq<Seq<ExtI64>>, n: nat, x: int, m: ExtI64) -> Seq<Seq<ExtI64>>
    recommends
        is_square_matrix(matrix, n),
        1 <= x < n,
        is_non_negative(m),
        m.is_int(),
{
    matrix.map(|i:int, seq:Seq<ExtI64>| {
        if i != x {
            seq.update(x, seq[0] - m)
        } else {
            matrix[0].map(|j:int, e:ExtI64|
                if j != x {
                    e + m
                } else {
                    matrix[x][x]
                }
            )
        }
    })
}

proof fn lem_reset(matrix: Seq<Seq<ExtI64>>, n: nat, x: int, m: ExtI64)
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
