from sympy import primerange
from math import gcd
from bisect import bisect_left, bisect_right
from itertools import combinations
import argparse
from tqdm import tqdm
import math


def repunits_for_base(p, d_min, d_max):
    """
    R_p(d) = (p^d - 1)/(p-1) を d_min..d_max の範囲で前計算

    Parameters
    ----------
    p : int
        基数（2以上の整数）
    d_min : int
        計算を開始する桁数（2以上）
    d_max : int
        計算を終了する桁数

    Returns
    -------
    list of tuple
        (d, R_p(d)) のタプルのリスト
    """
    arr = []
    R = 1  # d=1
    for d in range(2, d_max + 1):
        R = p * R + 1
        if d >= d_min:
            arr.append((d, R))
    return arr


def search_repd_tuples(
    prime_max=10,
    tuple_size=3,
    d_range=(2, 10),
    stop_after=None,  # 何件か見つけたら停止（None=全部）
):
    """
    指定された素数までの素数集合に対して、各p進数でゾロ目になる数を探索する。
    Parameters
    ----------
    prime_max : int
        探索に用いる素数の最大値
    tuple_size : int
        素数集合のサイズ
    d_range : tuple of int
        探索する桁数の範囲 (d_min, d_max)
    stop_after : int or None
        見つけたら探索を停止する件数（Noneの場合は全て探索）
    Returns
    -------
    list of dict
        条件を満たす解のリスト。各要素は辞書で、以下のキーを持つ。
        - "primes": tuple of int
            素数の組
        - "digits": tuple of int
            各素数に対応する桁数の組
        - "a": tuple of int
            各素数に対応するゾロ目の係数の組
        - "N": int
            それぞれの素数進数でゾロ目になる数
    """

    # p_k まで探索しきると返す
    d_min, d_max = d_range
    primes = list(primerange(2, prime_max + 1))

    print("Calculating Rp table...")
    Rp_table = {p: repunits_for_base(p, d_min, d_max) for p in primes}
    Rp_vals = {
        p: [R for d, R in Rp_table[p]] for p in primes
    }  # 探索用に値のみを並べた配列
    print("Rp table calculated.")

    results = []  # 例: {'primes':(p1,...,pk), 'digits':(n1,...,nk), 'a':(a1,...,ak), 'N':L}

    # —— 素数集合に対して候補を DFS
    def dfs_on_combo(p_combo):
        k = len(p_combo)

        # 素数を p_1 から p_idx まで採用したときの候補
        def dfs(idx, L, a_list, R_list, d_list, LB, UB):
            """
            深さ優先探索で素数の組み合わせに対してp進数で全てゾロ目になるような数を探索。
            結果をresultに格納する
            Args:
                idx (int): 現在探索している素数のインデックス
                L (int): 最小公倍数lcmの逐次計算の現在値
                a_list (list): 各素数に対応するゾロ目の係数のリスト
                R_list (list): 各素数に対応するRp値のリスト
                d_list (list): 各素数に対応する桁数のリスト
                LB (int): 探索範囲の下限
                UB (int): 探索範囲の上限
            Returns:
                None
            Side Effects:
                - 条件を満たす解が見つかった場合、resultsリストに辞書を追加
                - 辞書には"primes"(素数組)、"digits"(桁数)、"a"(係数)、"N"(lcm)を格納
            Notes:
                - idx == k に達すると探索終了し、結果をresultsに追加
                - 上限チェックにより、係数がp-1を超えないことを保証
                - 二分探索でRp_valsの探索範囲を効率化
                - stop_afterで指定された結果数に達すると探索を中断
            """

            # p_k まで探索しきると返す
            if idx == k:
                results.append(
                    {
                        "primes": p_combo,
                        "digits": tuple(d_list),
                        "a": tuple(a_list),
                        "N": L,
                    }
                )
                return

            p_new = p_combo[idx]
            R_pairs = Rp_table[p_new]
            R_vals = Rp_vals[p_new]

            # 探索範囲の設定
            lo = (LB + (p_new - 2)) // (p_new - 1)  # ceil(LB/(p-1))
            hi = UB

            # 二分探索で探索範囲に対応するインデックスを取得
            lo_idx = bisect_left(R_vals, lo)
            hi_idx = bisect_right(R_vals, hi)

            for t in range(lo_idx, hi_idx):
                d_new, R_new = R_pairs[t]

                # 探索範囲の更新
                LB_new = max(LB, R_new)
                UB_new = min(UB, (p_new - 1) * R_new)
                if LB_new > UB_new:
                    continue  # 探索打ち切り

                if idx == 0:
                    # 初期化
                    L_new = R_new  # lcm を逐次的に計算する変数
                    a_new = 1  # ゾロ目の値を逐次的に計算する変数
                    a_list_new = [a_new]  # 桁値のリスト
                else:
                    g = gcd(L, R_new)
                    ratio = R_new // g  # a を更新する倍率

                    # 既存 a_i を一斉更新して、上限を超えないかチェック
                    a_updated = []
                    over = False
                    for i, a_i in enumerate(a_list):
                        p_i = p_combo[i]
                        a_i2 = a_i * ratio
                        # 上限チェック（超えると繰り上がってしまう）
                        if a_i2 > p_i - 1:
                            over = True
                            break
                        a_updated.append(a_i2)
                    if over:
                        continue

                    # 新しい a についても上限チェック
                    a_new = L // g
                    if a_new > p_new - 1:
                        continue

                    # 更新
                    L_new = (L // g) * R_new
                    a_list_new = a_updated + [a_new]

                # 素数を一つ足して再び探索
                dfs(
                    idx + 1,
                    L_new,
                    a_list_new,
                    R_list + [R_new],
                    d_list + [d_new],
                    LB_new,
                    UB_new,
                )

                # 目標組数に達したら終了
                if stop_after is not None and len(results) >= stop_after:
                    return

        INF = 10**100  # 上界
        dfs(idx=0, L=1, a_list=[], R_list=[], d_list=[], LB=0, UB=INF)

    # k 組の素数集合を昇順で列挙（重複なし）
    print("Searching repdigit tuples...")
    for p_combo in tqdm(
        combinations(primes, tuple_size), total=math.comb(len(primes), tuple_size)
    ):
        dfs_on_combo(p_combo)
        if stop_after is not None and len(results) >= stop_after:
            break
    print("done.")

    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Search for repdigit tuples.")
    parser.add_argument(
        "--prime_max", type=int, help="Maximum prime number to consider", default=10
    )
    parser.add_argument(
        "--tuple_size", type=int, help="Size of the prime tuple", default=2
    )
    parser.add_argument(
        "--d_min", type=int, help="Minimum digit count (>= 2)", default=2
    )
    parser.add_argument("--d_max", type=int, help="Maximum digit count", default=5)
    parser.add_argument(
        "--stop_after",
        type=int,
        default=None,
        help="Stop after finding this many results (default: all)",
    )
    args = parser.parse_args()
    print(args)

    results = search_repd_tuples(
        prime_max=args.prime_max,
        tuple_size=args.tuple_size,
        d_range=(args.d_min, args.d_max),
        stop_after=args.stop_after,
    )
    for r in results:
        print(r)
