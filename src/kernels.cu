// ============================================================================
// `kernels.cu` — NVRTC CUDA C++ kernels for Erdős Problem #41 (Infinite B_3 Sets)
// ============================================================================
//
// Implements:
//   1. `k_dfs_b3_ruler`:
//      Reversible in-register O(1) bitset-shift branch-and-bound for exact B_3
//      capacities F_3(N) and shortest B_3 rulers (OEIS A051912).
//      Maintains:
//        - m1[2] : 1-element bitset M_1 = \sum_{a \in A} 2^a      (up to 127)
//        - m2[4] : 2-sum bitset     M_2 = \sum_{s \in A+A} 2^s    (up to 255)
//        - m3[6] : 3-sum bitset     M_3 = \sum_{t \in A+A+A} 2^t  (up to 383)
//      Because every B_3 set has unique 2-sums and unique 3-sums, pushing a
//      valid candidate x > max(A) sets only previously-zero bits, and popping x
//      reverses the transition in-place via XOR without storing masks on the
//      DFS stack.
//   2. `k_eval_b3_conservation`:
//      Batch GPU evaluator for Theorem 2.1(a) Exact (2,1)-Difference Harmonic
//      Conservation Identity and Theorem 2.1(b) Dyadic Shell Inequality.

typedef unsigned char      uint8_t;
typedef unsigned int       uint32_t;
typedef unsigned long long uint64_t;
typedef long long          int64_t;

__device__ __forceinline__ void set_bit(uint64_t* arr, int bit) {
    arr[bit >> 6] |= (1ULL << (bit & 63));
}

__device__ __forceinline__ void xor_bit(uint64_t* arr, int bit) {
    arr[bit >> 6] ^= (1ULL << (bit & 63));
}

// Returns true iff ((src << shift) & dst) != 0 over `src_words` words of `src`
// and `dst_words` words of `dst`.
__device__ __forceinline__ bool shift_overlaps(
    const uint64_t* src,
    int src_words,
    int shift,
    const uint64_t* dst,
    int dst_words
) {
    int word_shift = shift >> 6;
    int bit_shift  = shift & 63;
    if (bit_shift == 0) {
        for (int i = 0; i < src_words; ++i) {
            int j = i + word_shift;
            if (j < dst_words) {
                if ((src[i] & dst[j]) != 0ULL) return true;
            }
        }
    } else {
        int inv_shift = 64 - bit_shift;
        for (int i = 0; i < src_words; ++i) {
            uint64_t w = src[i];
            if (w == 0ULL) continue;
            int j0 = i + word_shift;
            if (j0 < dst_words) {
                if (((w << bit_shift) & dst[j0]) != 0ULL) return true;
            }
            int j1 = j0 + 1;
            if (j1 < dst_words) {
                if (((w >> inv_shift) & dst[j1]) != 0ULL) return true;
            }
        }
    }
    return false;
}

// Performs dst ^= (src << shift) over `src_words` words of `src`.
__device__ __forceinline__ void shift_xor_into(
    const uint64_t* src,
    int src_words,
    int shift,
    uint64_t* dst,
    int dst_words
) {
    int word_shift = shift >> 6;
    int bit_shift  = shift & 63;
    if (bit_shift == 0) {
        for (int i = 0; i < src_words; ++i) {
            int j = i + word_shift;
            if (j < dst_words) {
                dst[j] ^= src[i];
            }
        }
    } else {
        int inv_shift = 64 - bit_shift;
        for (int i = 0; i < src_words; ++i) {
            uint64_t w = src[i];
            if (w == 0ULL) continue;
            int j0 = i + word_shift;
            if (j0 < dst_words) {
                dst[j0] ^= (w << bit_shift);
            }
            int j1 = j0 + 1;
            if (j1 < dst_words) {
                dst[j1] ^= (w >> inv_shift);
            }
        }
    }
}

__device__ __forceinline__ bool can_add_b3(
    const uint64_t* m1,
    const uint64_t* m2,
    const uint64_t* m3,
    int x
) {
    // 1. Check (M_1 << x) & M_2 == 0  (B_2 condition)
    if (shift_overlaps(m1, 2, x, m2, 4)) return false;
    // 2. Check (M_2 << x) & M_3 == 0  (1-x vs 0-x 3-sum condition)
    if (shift_overlaps(m2, 4, x, m3, 6)) return false;
    // 3. Check (M_1 << 2x) & M_3 == 0 (2-x vs 0-x 3-sum condition)
    if (shift_overlaps(m1, 2, 2 * x, m3, 6)) return false;
    return true;
}

__device__ __forceinline__ void push_b3(
    uint64_t* m1,
    uint64_t* m2,
    uint64_t* m3,
    int x
) {
    shift_xor_into(m2, 4, x, m3, 6);
    shift_xor_into(m1, 2, 2 * x, m3, 6);
    xor_bit(m3, 3 * x);

    shift_xor_into(m1, 2, x, m2, 4);
    xor_bit(m2, 2 * x);

    xor_bit(m1, x);
}

__device__ __forceinline__ void pop_b3(
    uint64_t* m1,
    uint64_t* m2,
    uint64_t* m3,
    int x
) {
    xor_bit(m1, x);

    shift_xor_into(m1, 2, x, m2, 4);
    xor_bit(m2, 2 * x);

    shift_xor_into(m2, 4, x, m3, 6);
    shift_xor_into(m1, 2, 2 * x, m3, 6);
    xor_bit(m3, 3 * x);
}

extern "C" __global__ void k_dfs_b3_ruler(
    const uint64_t* __restrict__ prefix_m1,   // [n_prefixes * 2]
    const uint64_t* __restrict__ prefix_m2,   // [n_prefixes * 4]
    const uint64_t* __restrict__ prefix_m3,   // [n_prefixes * 6]
    const uint32_t* __restrict__ prefix_len,  // [n_prefixes]
    const uint32_t* __restrict__ prefix_last, // [n_prefixes]
    uint32_t n_prefixes,
    uint32_t n_max,
    uint32_t split_x,
    const uint8_t* __restrict__ req_prefix,   // [n_max + 1]
    const uint8_t* __restrict__ b3_cap,       // [n_max + 1]
    uint32_t* __restrict__ out_max_len,       // [n_prefixes]
    uint64_t* __restrict__ out_best_m1,       // [n_prefixes * 2]
    uint64_t* __restrict__ out_nodes          // [n_prefixes]
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_prefixes) return;

    uint64_t m1[2];
    uint64_t m2[4];
    uint64_t m3[6];

    for (int i = 0; i < 2; ++i) m1[i] = prefix_m1[idx * 2 + i];
    for (int i = 0; i < 4; ++i) m2[i] = prefix_m2[idx * 4 + i];
    for (int i = 0; i < 6; ++i) m3[i] = prefix_m3[idx * 6 + i];

    int base_len = (int)prefix_len[idx];
    int start_x  = (int)split_x + 1;
    int p_last   = (int)prefix_last[idx];
    if (p_last + 1 > start_x) {
        start_x = p_last + 1;
    }

    uint32_t best_len = 0;
    uint64_t best_m1_0 = 0ULL;
    uint64_t best_m1_1 = 0ULL;
    uint64_t nodes = 0ULL;

    // Check if prefix itself satisfies req_prefix up to n_max
    bool prefix_ok = true;
    for (int u = (int)split_x; u <= (int)n_max; ++u) {
        if (base_len < (int)req_prefix[u]) {
            prefix_ok = false;
            break;
        }
    }
    if (prefix_ok) {
        best_len  = (uint32_t)base_len;
        best_m1_0 = m1[0];
        best_m1_1 = m1[1];
    }

    // Reversible stack: stores only the added elements and next candidate x
    uint8_t added_x[16];
    uint8_t next_try[16];
    int depth = 0;
    next_try[0] = (uint8_t)start_x;

    while (depth >= 0) {
        int cur_len = base_len + depth;
        int x = (int)next_try[depth];

        if (x > (int)n_max) {
            depth--;
            if (depth >= 0) {
                pop_b3(m1, m2, m3, (int)added_x[depth]);
            }
            continue;
        }

        // Advance iterator at current depth before testing x
        next_try[depth] = (uint8_t)(x + 1);

        // Check prefix-floor constraint at u = x - 1:
        // If cur_len < req_prefix[x - 1], then neither x nor any y > x can
        // rescue the prefix count at x - 1, so we can immediately backtrack!
        if (cur_len < (int)req_prefix[x - 1]) {
            depth--;
            if (depth >= 0) {
                pop_b3(m1, m2, m3, (int)added_x[depth]);
            }
            continue;
        }

        // Subadditive B_3 tail-capacity pruning:
        // In [x, n_max] of width w = n_max - x + 1, at most b3_cap[w] elements can be added.
        int max_possible = cur_len + (int)b3_cap[(int)n_max - x + 1];
        if (max_possible < (int)req_prefix[n_max] || max_possible <= (int)best_len) {
            depth--;
            if (depth >= 0) {
                pop_b3(m1, m2, m3, (int)added_x[depth]);
            }
            continue;
        }

        nodes += 1ULL;

        if (can_add_b3(m1, m2, m3, x)) {
            int new_len = cur_len + 1;
            push_b3(m1, m2, m3, x);

            // Check if this extended set is already a valid global improvement
            if (new_len > (int)best_len) {
                bool tail_ok = true;
                for (int u = x; u <= (int)n_max; ++u) {
                    if (new_len < (int)req_prefix[u]) {
                        tail_ok = false;
                        break;
                    }
                }
                if (tail_ok) {
                    best_len  = (uint32_t)new_len;
                    best_m1_0 = m1[0];
                    best_m1_1 = m1[1];
                }
            }

            if (x < (int)n_max && depth + 1 < 16) {
                added_x[depth] = (uint8_t)x;
                depth++;
                next_try[depth] = (uint8_t)(x + 1);
            } else {
                pop_b3(m1, m2, m3, x);
            }
        }
    }

    out_max_len[idx]         = best_len;
    out_best_m1[idx * 2 + 0] = best_m1_0;
    out_best_m1[idx * 2 + 1] = best_m1_1;
    out_nodes[idx]           = nodes;
}

extern "C" __global__ void k_eval_b3_conservation(
    const uint32_t* __restrict__ sets,    // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths, // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t horizon_n,
    double* __restrict__ out_energy,      // \mathcal{E}_A^{(3)}(N)
    double* __restrict__ out_defect,      // \Delta_A^{(2,1)}(N)
    double* __restrict__ out_budget,      // \mathcal{B}_A^{(2,1)}(N)
    uint32_t* __restrict__ out_is_b3      // 1 if valid B_3, 0 otherwise
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;

    double energy = 0.0;
    double defect = 0.0;
    double budget = 0.0;
    uint32_t is_b3 = 1;

    // Verify B_2 and ordered (2,1)-difference injectivity while accumulating
    // Theorem 2.1(a) quantities.
    for (uint32_t k = 1; k < m; ++k) {
        double ak = (double)a[k];
        if (ak > (double)horizon_n) break;
        double k_choose_2 = 0.5 * (double)k * (double)(k + 1);
        energy += k_choose_2 / ak;

        for (uint32_t j = 0; j < k; ++j) {
            for (uint32_t i = 0; i <= j; ++i) {
                int w = (int)a[k] - (int)a[i] - (int)a[j];
                int abs_w = w >= 0 ? w : -w;
                double denom = (double)(abs_w + 2);
                budget += 1.0 / denom;
                defect += (ak - denom) / (denom * ak);
            }
        }
    }

    // Check 3-sum collision freedom for small m <= 32
    if (m <= 32) {
        for (uint32_t i1 = 0; i1 < m && is_b3; ++i1) {
            for (uint32_t j1 = i1; j1 < m && is_b3; ++j1) {
                for (uint32_t k1 = j1; k1 < m && is_b3; ++k1) {
                    uint32_t s1 = a[i1] + a[j1] + a[k1];
                    for (uint32_t i2 = i1; i2 < m && is_b3; ++i2) {
                        uint32_t j2_start = (i2 == i1) ? j1 : i2;
                        for (uint32_t j2 = j2_start; j2 < m && is_b3; ++j2) {
                            uint32_t k2_start = (i2 == i1 && j2 == j1) ? (k1 + 1) : j2;
                            for (uint32_t k2 = k2_start; k2 < m; ++k2) {
                                if (a[i2] + a[j2] + a[k2] == s1) {
                                    is_b3 = 0;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    out_energy[idx] = energy;
    out_defect[idx] = defect;
    out_budget[idx] = budget;
    out_is_b3[idx]  = is_b3;
}

extern "C" __global__ void k_eval_b3_sign_cones(
    const uint32_t* __restrict__ sets,       // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,    // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t horizon_n,
    double* __restrict__ out_pos_energy,     // \mathcal{E}_A^+(N)
    double* __restrict__ out_pos_defect,     // \Delta_A^+(N)
    double* __restrict__ out_pos_budget,     // \mathcal{B}_A^+(N)
    double* __restrict__ out_neg_energy,     // \mathcal{E}_A^-(N)
    double* __restrict__ out_neg_defect,     // \Delta_A^-(N)
    double* __restrict__ out_neg_budget,     // \mathcal{B}_A^-(N)
    uint32_t* __restrict__ out_pos_count,    // |\mathcal{T}_m^+|
    uint32_t* __restrict__ out_zero_count,   // |\mathcal{T}_m^0| <= 1
    uint32_t* __restrict__ out_neg_count     // |\mathcal{T}_m^-|
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;

    double pos_energy = 0.0;
    double pos_defect = 0.0;
    double pos_budget = 0.0;
    double neg_energy = 0.0;
    double neg_defect = 0.0;
    double neg_budget = 0.0;
    uint32_t pos_cnt = 0;
    uint32_t zero_cnt = 0;
    uint32_t neg_cnt = 0;

    for (uint32_t k = 1; k < m; ++k) {
        if (a[k] > horizon_n) break;
        double ak = (double)a[k];
        for (uint32_t j = 0; j < k; ++j) {
            for (uint32_t i = 0; i <= j; ++i) {
                int w = (int)a[k] - (int)a[i] - (int)a[j];
                if (w > 0) {
                    pos_cnt += 1;
                    double denom = (double)(w + 2);
                    double num = (double)(a[i] + a[j]) - 2.0;
                    pos_energy += 1.0 / ak;
                    pos_defect += num / (denom * ak);
                    pos_budget += 1.0 / denom;
                } else if (w == 0) {
                    zero_cnt += 1;
                } else {
                    neg_cnt += 1;
                    int u = -w;
                    double denom = (double)(u + 2);
                    double num = 2.0 * ak - (double)(a[i] + a[j]) - 2.0;
                    neg_energy += 1.0 / ak;
                    neg_defect += num / (denom * ak);
                    neg_budget += 1.0 / denom;
                }
            }
        }
    }

    out_pos_energy[idx] = pos_energy;
    out_pos_defect[idx] = pos_defect;
    out_pos_budget[idx] = pos_budget;
    out_neg_energy[idx] = neg_energy;
    out_neg_defect[idx] = neg_defect;
    out_neg_budget[idx] = neg_budget;
    out_pos_count[idx]  = pos_cnt;
    out_zero_count[idx] = zero_cnt;
    out_neg_count[idx]  = neg_cnt;
}

extern "C" __global__ void k_eval_b3_full_cube(
    const uint32_t* __restrict__ sets,              // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,           // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t* __restrict__ out_total_triples,       // T_m = m^2(m-1)/2
    uint32_t* __restrict__ out_one_sided_triples,   // |\mathcal{I}_m^{<}| = m(m-1)(2m-1)/6
    double* __restrict__ out_mean_w,                // \bar{w} = \bar{a}
    double* __restrict__ out_var_w,                 // \mathrm{Var}_{\mathcal{I}_m}(w)
    double* __restrict__ out_theoretical_var_w,     // 3(m+1)/(m-1) * \sigma_A^2
    double* __restrict__ out_one_sided_budget       // \sum_{(i,j,k) \in \mathcal{I}_m^{<}} 1 / (a_i + a_j - a_k - 1)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;
    if (m < 3) {
        out_total_triples[idx]     = 0;
        out_one_sided_triples[idx] = 0;
        out_mean_w[idx]            = 0.0;
        out_var_w[idx]             = 0.0;
        out_theoretical_var_w[idx] = 0.0;
        out_one_sided_budget[idx]  = 0.0;
        return;
    }

    double sum_a = 0.0;
    for (uint32_t r = 0; r < m; ++r) {
        sum_a += (double)a[r];
    }
    double mean_a = sum_a / (double)m;

    double sum_sq_a = 0.0;
    for (uint32_t r = 0; r < m; ++r) {
        double d = (double)a[r] - mean_a;
        sum_sq_a += d * d;
    }
    double sigma_a_sq = sum_sq_a / (double)m;

    uint32_t total_cnt = 0;
    uint32_t one_sided_cnt = 0;
    double sum_w = 0.0;
    double sum_sq_w = 0.0;
    double one_sided_budget = 0.0;

    for (uint32_t i = 0; i < m; ++i) {
        for (uint32_t j = i; j < m; ++j) {
            for (uint32_t k = 0; k < m; ++k) {
                if (k == i || k == j) continue;
                total_cnt += 1;
                int w = (int)a[i] + (int)a[j] - (int)a[k];
                double wf = (double)w;
                sum_w += wf;
                double dev = wf - mean_a;
                sum_sq_w += dev * dev;
                if (k < j) {
                    one_sided_cnt += 1;
                    one_sided_budget += 1.0 / (double)(w - 1);
                }
            }
        }
    }

    out_total_triples[idx]     = total_cnt;
    out_one_sided_triples[idx] = one_sided_cnt;
    out_mean_w[idx]            = sum_w / (double)total_cnt;
    out_var_w[idx]             = sum_sq_w / (double)total_cnt;
    out_theoretical_var_w[idx] = (3.0 * (double)(m + 1) / (double)(m - 1)) * sigma_a_sq;
    out_one_sided_budget[idx]  = one_sided_budget;
}

extern "C" __global__ void k_eval_sublevel_subcone_weights(
    const uint32_t* __restrict__ sets,              // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,           // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint64_t tau_num,
    uint64_t tau_den,
    uint32_t* __restrict__ out_full_triples,        // N_m^< = m(m-1)(2m-1)/6
    int64_t* __restrict__ out_full_sum,             // \sum_{(i,j,k) \in \mathcal{I}_m^{<}} (a_i + a_j - a_k)
    int64_t* __restrict__ out_full_poly_rhs,        // \sum_{r=1}^m (r^2 - m) a_r
    uint32_t* __restrict__ out_sublevel_triples,    // |\Omega_\tau(m)|
    int64_t* __restrict__ out_sublevel_sum,         // \sum_{(i,j,k) \in \Omega_\tau(m)} (a_i + a_j - a_k)
    int64_t* __restrict__ out_sublevel_ref_sum,     // \sum_{(i,j,k) \in \Omega_\tau(m)} (i^3 + j^3 - k^3)
    int64_t* __restrict__ out_weights,              // [n_sets * max_m] discrete weights C_r(m, \tau)
    int64_t* __restrict__ out_min_weight            // \min_{1 <= r <= m} C_r(m, \tau)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;
    int64_t* w_row = out_weights + idx * max_m;

    for (uint32_t r = 0; r < max_m; ++r) {
        w_row[r] = 0;
    }

    if (m < 2) {
        out_full_triples[idx]     = 0;
        out_full_sum[idx]         = 0;
        out_full_poly_rhs[idx]    = 0;
        out_sublevel_triples[idx] = 0;
        out_sublevel_sum[idx]     = 0;
        out_sublevel_ref_sum[idx] = 0;
        out_min_weight[idx]       = 0;
        return;
    }

    uint64_t m64 = (uint64_t)m;
    uint64_t rhs_thresh = tau_num * m64 * m64 * m64;

    uint32_t full_cnt = 0;
    int64_t full_sum = 0;
    uint32_t sub_cnt = 0;
    int64_t sub_sum = 0;
    int64_t sub_ref_sum = 0;

    for (uint32_t i = 0; i < m; ++i) {
        uint64_t i1 = (uint64_t)(i + 1);
        uint64_t i3 = i1 * i1 * i1;
        for (uint32_t j = i; j < m; ++j) {
            uint64_t j1 = (uint64_t)(j + 1);
            uint64_t ij3 = i3 + j1 * j1 * j1;
            for (uint32_t k = 0; k < j; ++k) {
                if (k == i) continue;
                uint64_t k1 = (uint64_t)(k + 1);
                uint64_t ref_cube = ij3 - k1 * k1 * k1;
                int64_t w = (int64_t)a[i] + (int64_t)a[j] - (int64_t)a[k];

                full_cnt += 1;
                full_sum += w;

                if (tau_den * ref_cube <= rhs_thresh) {
                    sub_cnt += 1;
                    sub_sum += w;
                    sub_ref_sum += (int64_t)ref_cube;
                    w_row[i] += 1;
                    w_row[j] += 1;
                    w_row[k] -= 1;
                }
            }
        }
    }

    int64_t poly_rhs = 0;
    int64_t min_w = w_row[0];
    for (uint32_t r = 0; r < m; ++r) {
        int64_t r1 = (int64_t)(r + 1);
        poly_rhs += (r1 * r1 - (int64_t)m) * (int64_t)a[r];
        if (w_row[r] < min_w) {
            min_w = w_row[r];
        }
    }

    out_full_triples[idx]     = full_cnt;
    out_full_sum[idx]         = full_sum;
    out_full_poly_rhs[idx]    = poly_rhs;
    out_sublevel_triples[idx] = sub_cnt;
    out_sublevel_sum[idx]     = sub_sum;
    out_sublevel_ref_sum[idx] = sub_ref_sum;
    out_min_weight[idx]       = min_w;
}

__device__ __forceinline__ double d_odd_bp_inner_antideriv_p5(double delta, double z_lo, double z_hi) {
    const double pi = 3.14159265358979323846264338327950288;
    double a = pow(1.0 + delta, 0.2);
    double a4 = a * a * a * a;
    double denom = 25.0 * a4;

    double vals[2];
    double zs[2] = {z_lo, z_hi};
    for (int k = 0; k < 2; ++k) {
        double u = zs[k] / a;
        double acc = -log(1.0 - u);
        for (int m = 1; m <= 2; ++m) {
            double theta = 2.0 * pi * (double)m / 5.0;
            double ct = cos(theta);
            double st = sin(theta);
            acc -= ct * log(1.0 - 2.0 * u * ct + u * u);
            acc += 2.0 * st * atan((u - ct) / st);
        }
        vals[k] = acc / denom;
    }
    return vals[1] - vals[0];
}

extern "C" __global__ void k_eval_bp_projective_fermat(
    uint32_t n_grid,
    uint32_t n_laurent,
    double* __restrict__ out_slice_ord,   // [n_grid] outer t_1 slice of K_{*, 5}
    double* __restrict__ out_slice_prod,  // [n_grid] outer t_1 slice of K_{*, 5}^{prod}
    double* __restrict__ out_alpha,       // [n_laurent] exact Laurent \alpha_n (n = idx + 1)
    double* __restrict__ out_beta         // [n_laurent] exact Laurent \beta_n  (n = idx + 1)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n_laurent) {
        uint32_t n = idx + 1;
        double c_n = 1.0;
        double prod_beta_v = 1.0;
        for (uint32_t j = 1; j <= n; ++j) {
            double jf = (double)j;
            double factor = (j == 1) ? (1.0 / 3.0) : (((jf - 1.0) - (1.0 / 3.0)) / jf);
            c_n *= factor;
            prod_beta_v *= (3.0 * jf) / (3.0 * jf + 1.0);
        }
        double nf = (double)n;
        double alpha_n = c_n * prod_beta_v / (3.0 * nf - 2.0);
        double beta_n = alpha_n * (3.0 * nf + 1.0) / (3.0 * nf + 4.0);
        out_alpha[idx] = alpha_n;
        out_beta[idx]  = beta_n;
    }

    if (idx >= n_grid) return;

    double dt = 1.0 / (double)n_grid;
    double t1 = ((double)idx + 0.5) * dt;
    double t1_2 = t1 * t1;
    double t1_5 = t1_2 * t1_2 * t1;

    double slice_ord = 0.0;
    double slice_prod = 0.0;

    for (uint32_t i2 = 0; i2 < n_grid; ++i2) {
        double t2 = ((double)i2 + 0.5) * dt;
        double t2_2 = t2 * t2;
        double t2_5 = t2_2 * t2_2 * t2;
        double dz1 = t2 / (double)n_grid;
        double w_cell = dt * dt * dz1;

        for (uint32_t j1 = 0; j1 < n_grid; ++j1) {
            double z1 = ((double)j1 + 0.5) * dz1;
            double z1_2 = z1 * z1;
            double z1_5 = z1_2 * z1_2 * z1;
            double delta = t1_5 + t2_5 - z1_5;

            if (i2 >= idx) {
                double w_sym = (idx == i2) ? (0.5 * w_cell) : w_cell;
                slice_prod += d_odd_bp_inner_antideriv_p5(delta, 0.0, 1.0) * w_sym;
                slice_ord += d_odd_bp_inner_antideriv_p5(delta, z1, 1.0) * w_sym;
            }
        }
    }

    out_slice_ord[idx]  = slice_ord;
    out_slice_prod[idx] = slice_prod;
}

extern "C" __global__ void k_eval_three_hemisphere_cone(
    const uint32_t* __restrict__ sets,    // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths, // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t* __restrict__ out_lo_cnt,      // |\mathcal{I}_m^{lo}| = \binom{m+1}{3}
    uint32_t* __restrict__ out_mid_cnt,     // |\mathcal{I}_m^{mid}| = \binom{m}{3}
    uint32_t* __restrict__ out_hi_pos_cnt,  // |\mathcal{T}_m^-|
    uint32_t* __restrict__ out_hi_nonpos,   // |\mathcal{T}_m^+ \sqcup \mathcal{T}_m^0|
    int64_t* __restrict__ out_lo_sum,       // \sum_{\mathcal{I}_m^{lo}} (a_i + a_j - a_k)
    int64_t* __restrict__ out_mid_sum,      // \sum_{\mathcal{I}_m^{mid}} (a_i + a_j - a_k)
    int64_t* __restrict__ out_hi_pos_sum    // \sum_{\mathcal{T}_m^-} (a_i + a_j - a_k)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;

    uint32_t lo_cnt = 0;
    uint32_t mid_cnt = 0;
    uint32_t hi_pos_cnt = 0;
    uint32_t hi_nonpos_cnt = 0;
    int64_t lo_sum = 0;
    int64_t mid_sum = 0;
    int64_t hi_pos_sum = 0;

    for (uint32_t i = 0; i < m; ++i) {
        for (uint32_t j = i; j < m; ++j) {
            for (uint32_t k = 0; k < m; ++k) {
                if (k == i || k == j) continue;
                int64_t w = (int64_t)a[i] + (int64_t)a[j] - (int64_t)a[k];
                if (k < i) {
                    lo_cnt += 1;
                    lo_sum += w;
                } else if (k < j) {
                    mid_cnt += 1;
                    mid_sum += w;
                } else if (w > 0) {
                    hi_pos_cnt += 1;
                    hi_pos_sum += w;
                } else {
                    hi_nonpos_cnt += 1;
                }
            }
        }
    }

    out_lo_cnt[idx]     = lo_cnt;
    out_mid_cnt[idx]    = mid_cnt;
    out_hi_pos_cnt[idx] = hi_pos_cnt;
    out_hi_nonpos[idx]  = hi_nonpos_cnt;
    out_lo_sum[idx]     = lo_sum;
    out_mid_sum[idx]    = mid_sum;
    out_hi_pos_sum[idx] = hi_pos_sum;
}

__device__ __forceinline__ double d_odd_bp_inner_antideriv_to_one_smooth_p5(double delta, double z_lo) {
    const double pi = 3.14159265358979323846264338327950288;
    double a = pow(1.0 + delta, 0.2);
    double a2 = a * a;
    double a3 = a2 * a;
    double a4 = a2 * a2;
    double a5 = a4 * a;
    double denom = 25.0 * a4;
    double u_hi = 1.0 / a;
    double u_lo = z_lo / a;

    double sum_a_pow = a + a2 + a3 + a4 + a5;
    double acc = (log(sum_a_pow) - log(delta)) + log(1.0 - u_lo);
    for (int m = 1; m <= 2; ++m) {
        double theta = 2.0 * pi * (double)m / 5.0;
        double ct = cos(theta);
        double st = sin(theta);
        double q_hi = 1.0 - 2.0 * u_hi * ct + u_hi * u_hi;
        double q_lo = 1.0 - 2.0 * u_lo * ct + u_lo * u_lo;
        acc -= ct * (log(q_hi) - log(q_lo));
        acc += 2.0 * st * (atan((u_hi - ct) / st) - atan((u_lo - ct) / st));
    }
    return acc / denom;
}

extern "C" __global__ void k_eval_telescoping_third_hemisphere(
    const uint32_t* __restrict__ sets,       // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,    // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t n_grid_p5,
    uint32_t* __restrict__ out_all_exact,    // 1 if all (i, s) rays telescope & satisfy Markov bound
    int64_t* __restrict__ out_step1_sum,     // \sum_{i=1}^{m-1} \sum_{j=i}^{m-1} (a_i + a_j - a_{j+1})
    int64_t* __restrict__ out_step1_rhs,     // \sum_{i=1}^{m-1} ((m - i + 1) a_i - a_m)
    uint32_t* __restrict__ out_step1_pos,    // \sum_{i=1}^{m-1} |\{j \in [i, m-1] : a_i + a_j - a_{j+1} > 0\}|
    int64_t* __restrict__ out_upper_sum,     // \sum_{1 <= i <= j < k <= m} (a_i + a_j - a_k)
    int64_t* __restrict__ out_upper_rhs,     // \sum_{r=1}^m (m(m+1)/2 - r^2) a_r
    double* __restrict__ out_r3_slice_ord,   // [n_grid_p5] outer t_1 slice of K_{*, 5}^{III}
    double* __restrict__ out_r3_slice_prod   // [n_grid_p5] outer t_1 slice of K_{*, 5}^{prod, III}
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n_sets) {
        uint32_t m = lengths[idx];
        const uint32_t* a = sets + idx * max_m;

        uint32_t all_ok = 1;
        int64_t step1_sum = 0;
        int64_t step1_rhs = 0;
        uint32_t step1_pos = 0;

        for (uint32_t i = 0; i + 1 < m; ++i) {
            int64_t ai = (int64_t)a[i];
            for (uint32_t s = 1; s <= m - 1 - i; ++s) {
                int64_t num_terms = (int64_t)(m - s - i);
                int64_t lhs = 0;
                uint32_t pos_cnt = 0;
                for (uint32_t j = i; j < m - s; ++j) {
                    int64_t w = ai + (int64_t)a[j] - (int64_t)a[j + s];
                    lhs += w;
                    if (w > 0) pos_cnt += 1;
                }
                int64_t head_sum = 0;
                int64_t tail_sum = 0;
                for (uint32_t r = 0; r < s; ++r) {
                    head_sum += (int64_t)a[i + r];
                    tail_sum += (int64_t)a[m - s + r];
                }
                int64_t rhs = num_terms * ai + head_sum - tail_sum;
                if (lhs != rhs || ((int64_t)pos_cnt * ai < rhs)) {
                    all_ok = 0;
                }
                if (s == 1) {
                    step1_sum += lhs;
                    step1_rhs += (int64_t)(m - i) * ai - (int64_t)a[m - 1];
                    step1_pos += pos_cnt;
                }
            }
        }

        int64_t upper_sum = 0;
        for (uint32_t i = 0; i < m; ++i) {
            for (uint32_t j = i; j < m; ++j) {
                for (uint32_t k = j + 1; k < m; ++k) {
                    upper_sum += (int64_t)a[i] + (int64_t)a[j] - (int64_t)a[k];
                }
            }
        }

        int64_t mf = (int64_t)m;
        int64_t half_m_mp1 = mf * (mf + 1) / 2;
        int64_t upper_rhs = 0;
        for (uint32_t r_idx = 0; r_idx < m; ++r_idx) {
            int64_t r = (int64_t)(r_idx + 1);
            upper_rhs += (half_m_mp1 - r * r) * (int64_t)a[r_idx];
        }

        out_all_exact[idx] = all_ok;
        out_step1_sum[idx] = step1_sum;
        out_step1_rhs[idx] = step1_rhs;
        out_step1_pos[idx] = step1_pos;
        out_upper_sum[idx] = upper_sum;
        out_upper_rhs[idx] = upper_rhs;
    }

    if (idx < n_grid_p5) {
        double dt = 1.0 / (double)n_grid_p5;
        double t1 = ((double)idx + 0.5) * dt;
        double t1_2 = t1 * t1;
        double t1_5 = t1_2 * t1_2 * t1;

        double r3_ord = 0.0;
        double r3_prod = 0.0;
        double du = 1.0 / (double)n_grid_p5;

        for (uint32_t i2 = idx; i2 < n_grid_p5; ++i2) {
            double t2 = ((double)i2 + 0.5) * dt;
            double t2_2 = t2 * t2;
            double t2_5 = t2_2 * t2_2 * t2;
            double w_sym = (idx == i2) ? (0.5 * dt * dt) : (dt * dt);
            double z1_max = pow(t1_5 + t2_5, 0.2);
            if (z1_max > 1.0) z1_max = 1.0;

            if (z1_max > t2) {
                double span = z1_max - t2;
                for (uint32_t j1 = 0; j1 < n_grid_p5; ++j1) {
                    double u = ((double)j1 + 0.5) * du;
                    double z1 = t2 + span * (1.0 - u * u);
                    double dz1 = span * 2.0 * u * du;
                    double z1_2 = z1 * z1;
                    double z1_5 = z1_2 * z1_2 * z1;
                    double delta = t1_5 + t2_5 - z1_5;
                    if (delta > 0.0 && z1 < 1.0) {
                        double w_cell = w_sym * dz1;
                        r3_ord  += d_odd_bp_inner_antideriv_to_one_smooth_p5(delta, z1) * w_cell;
                        r3_prod += d_odd_bp_inner_antideriv_to_one_smooth_p5(delta, 0.0) * w_cell;
                    }
                }
            }
        }

        out_r3_slice_ord[idx]  = r3_ord;
        out_r3_slice_prod[idx] = r3_prod;
    }
}

extern "C" __global__ void k_eval_horizon_truncated_rays(
    const uint32_t* __restrict__ sets,              // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,           // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t n_grid_u,
    uint32_t* __restrict__ out_all_exact_valid,     // 1 if all (i, s, K) identities & bounds hold
    uint32_t* __restrict__ out_actual_pos,          // |\mathcal{T}_m^-|
    uint32_t* __restrict__ out_untrunc_markov,      // K = m coarse Markov certified count
    uint32_t* __restrict__ out_untrunc_mingap,      // K = m min-gap certified count
    uint32_t* __restrict__ out_trunc_markov,        // \max_{K} coarse Markov certified count
    uint32_t* __restrict__ out_trunc_mingap,        // \max_{K} min-gap certified count
    uint32_t* __restrict__ out_untrunc_active_rays, // active rays at K = m
    uint32_t* __restrict__ out_trunc_active_rays,   // active rays under optimal K \in [i+s, m]
    double* __restrict__ out_u_slice_p3,            // [n_grid_u] outer u-slice of \Phi_3 / u^3 integral
    double* __restrict__ out_u_slice_p5             // [n_grid_u] outer u-slice of \Phi_5 / u^5 integral
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n_sets) {
        uint32_t m = lengths[idx];
        const uint32_t* a = sets + idx * max_m;

        uint32_t all_ok = 1;
        uint32_t actual_pos_tot = 0;
        uint32_t untrunc_m_tot = 0;
        uint32_t untrunc_g_tot = 0;
        uint32_t trunc_m_tot = 0;
        uint32_t trunc_g_tot = 0;
        uint32_t untrunc_act = 0;
        uint32_t trunc_act = 0;

        for (uint32_t i = 0; i + 1 < m; ++i) {
            int64_t ai = (int64_t)a[i];
            for (uint32_t s = 1; s <= m - 1 - i; ++s) {
                uint32_t actual_pos = 0;
                for (uint32_t j = i; j < m - s; ++j) {
                    if (ai + (int64_t)a[j] - (int64_t)a[j + s] >= 1) {
                        actual_pos += 1;
                    }
                }
                actual_pos_tot += actual_pos;

                int64_t head_sum = 0;
                for (uint32_t r = 0; r < s; ++r) {
                    head_sum += (int64_t)a[i + r];
                }

                uint32_t best_m = 0;
                uint32_t best_g = 0;
                uint32_t untrunc_m = 0;
                uint32_t untrunc_g = 0;

                for (uint32_t k_hor = i + s + 1; k_hor <= m; ++k_hor) {
                    int64_t num_terms = (int64_t)(k_hor - s - i);
                    int64_t lhs = 0;
                    uint32_t pos_k = 0;
                    for (uint32_t j = i; j < k_hor - s; ++j) {
                        int64_t w = ai + (int64_t)a[j] - (int64_t)a[j + s];
                        lhs += w;
                        if (w >= 1) pos_k += 1;
                    }
                    int64_t tail_sum = 0;
                    for (uint32_t r = 0; r < s; ++r) {
                        tail_sum += (int64_t)a[k_hor - s + r];
                    }
                    int64_t rhs = num_terms * ai + head_sum - tail_sum;
                    if (lhs != rhs) {
                        all_ok = 0;
                    }

                    uint32_t c_m = (rhs > 0) ? (uint32_t)((rhs + ai - 1) / ai) : 0;
                    int64_t denom_g = ai - (int64_t)s;
                    if (denom_g < 1) denom_g = 1;
                    uint32_t c_g = (rhs > 0) ? (uint32_t)((rhs + denom_g - 1) / denom_g) : 0;

                    if (!(c_m <= c_g && c_g <= pos_k && pos_k <= actual_pos)) {
                        all_ok = 0;
                    }

                    if (c_m > best_m) best_m = c_m;
                    if (c_g > best_g) best_g = c_g;
                    if (k_hor == m) {
                        untrunc_m = c_m;
                        untrunc_g = c_g;
                    }
                }

                untrunc_m_tot += untrunc_m;
                untrunc_g_tot += untrunc_g;
                trunc_m_tot   += best_m;
                trunc_g_tot   += best_g;
                if (untrunc_g > 0) untrunc_act += 1;
                if (best_g > 0)    trunc_act += 1;
            }
        }

        out_all_exact_valid[idx]     = all_ok;
        out_actual_pos[idx]          = actual_pos_tot;
        out_untrunc_markov[idx]      = untrunc_m_tot;
        out_untrunc_mingap[idx]      = untrunc_g_tot;
        out_trunc_markov[idx]        = trunc_m_tot;
        out_trunc_mingap[idx]        = trunc_g_tot;
        out_untrunc_active_rays[idx] = untrunc_act;
        out_trunc_active_rays[idx]   = trunc_act;
    }

    if (idx < n_grid_u) {
        double du = 1.0 / (double)n_grid_u;
        double u = ((double)idx + 0.5) * du;
        double u2 = u * u;
        double u3 = u2 * u;
        double u5 = u3 * u2;

        double dsigma_p3 = (u / 3.0) / (double)n_grid_u;
        double dsigma_p5 = (u / 5.0) / (double)n_grid_u;
        double slice_p3 = 0.0;
        double slice_p5 = 0.0;

        for (uint32_t isig = 0; isig < n_grid_u; ++isig) {
            double sig3 = ((double)isig + 0.5) * dsigma_p3;
            double k3 = sqrt(u3 / (3.0 * sig3));
            if (k3 > 1.0) k3 = 1.0;
            double phi3 = (k3 - u) - sig3 * (k3 * k3 * k3 - u3) / u3;
            if (phi3 > 0.0) slice_p3 += phi3 * du * dsigma_p3;

            double sig5 = ((double)isig + 0.5) * dsigma_p5;
            double k5 = pow(u5 / (5.0 * sig5), 0.25);
            if (k5 > 1.0) k5 = 1.0;
            double k5_2 = k5 * k5;
            double k5_5 = k5_2 * k5_2 * k5;
            double phi5 = (k5 - u) - sig5 * (k5_5 - u5) / u5;
            if (phi5 > 0.0) slice_p5 += phi5 * du * dsigma_p5;
        }

        out_u_slice_p3[idx] = slice_p3;
        out_u_slice_p5[idx] = slice_p5;
    }
}

__device__ __forceinline__ uint32_t d_quad_injection_count(int64_t s_val, int64_t m_ceil) {
    if (s_val <= 0) return 0;
    int64_t m_pos = (m_ceil > 1) ? m_ceil : 1;
    if (2 * s_val >= m_pos * (m_pos + 1)) {
        return (uint32_t)m_pos;
    }
    double mf = (double)m_pos;
    double disc = (mf + 0.5) * (mf + 0.5) - 2.0 * (double)s_val;
    if (disc < 0.0) disc = 0.0;
    int64_t c = (int64_t)ceil(mf + 0.5 - sqrt(disc));
    if (c < 1) c = 1;
    if (c > m_pos) c = m_pos;
    while (c > 1 && (c - 1) * (2 * m_pos + 1 - (c - 1)) >= 2 * s_val) {
        c -= 1;
    }
    while (c < m_pos && c * (2 * m_pos + 1 - c) < 2 * s_val) {
        c += 1;
    }
    return (uint32_t)c;
}

extern "C" __global__ void k_eval_quadratic_injection_rays(
    const uint32_t* __restrict__ sets,              // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,           // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t* __restrict__ out_all_ok,              // 1 if all window identities & injection bounds hold
    uint32_t* __restrict__ out_actual_pos,          // |\mathcal{T}_m^-|
    uint32_t* __restrict__ out_trunc_sidon_quad,    // single-horizon (J = i) Sidon-ceiling quad count
    uint32_t* __restrict__ out_win_sidon_quad,      // two-sided window (J >= i) Sidon-ceiling quad count
    uint32_t* __restrict__ out_trunc_raygap_quad,   // single-horizon (J = i) ray-min-gap quad count
    int64_t* __restrict__ out_total_si_star,        // \sum_{i=1}^{m-1} S_i^*
    uint32_t* __restrict__ out_slot_evict_cnt,      // C_{\mathrm{evict}}
    int64_t* __restrict__ out_poly_lhs,             // \sum_{r=1}^m (r^2 - m) a_r
    int64_t* __restrict__ out_base_rhs,             // \binom{N_m^< + 1}{2}
    int64_t* __restrict__ out_evict_rhs             // \binom{N_m^< + C_{\mathrm{evict}} + 1}{2} - \sum_{i, s} (...)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_sets) return;

    uint32_t m = lengths[idx];
    const uint32_t* a = sets + idx * max_m;

    uint32_t all_ok = 1;
    uint32_t actual_pos_tot = 0;
    uint32_t trunc_sid_tot = 0;
    uint32_t win_sid_tot = 0;
    uint32_t trunc_rg_tot = 0;
    int64_t total_si_star = 0;

    int64_t mf = (int64_t)m;
    int64_t n_lt = mf * (mf - 1) * (2 * mf - 1) / 6;
    int64_t c_evict = 0;
    int64_t upper_w_sum = 0;

    for (uint32_t i = 0; i + 1 < m; ++i) {
        int64_t ai = (int64_t)a[i];
        int64_t si_star = 0;
        uint32_t ci_actual = 0;

        for (uint32_t s = 1; s <= m - 1 - i; ++s) {
            int64_t s_i64 = (int64_t)s;
            int64_t m_sid = ai - s_i64 * (s_i64 + 1) / 2;
            if (m_sid < 1) m_sid = 1;
            int64_t m_mg = ai - s_i64;
            if (m_mg < 1) m_mg = 1;

            uint32_t actual_pos = 0;
            for (uint32_t j = i; j < m - s; ++j) {
                if (ai + (int64_t)a[j] - (int64_t)a[j + s] >= 1) {
                    actual_pos += 1;
                }
            }
            actual_pos_tot += actual_pos;
            ci_actual += actual_pos;

            int64_t best_s_trunc = 0;
            uint32_t best_q_sid_trunc = 0;
            uint32_t best_q_rg_trunc = 0;
            uint32_t best_q_sid_win = 0;

            for (uint32_t j_start = i; j_start < m - s; ++j_start) {
                int64_t head_sum = 0;
                for (uint32_t r = 0; r < s; ++r) {
                    head_sum += (int64_t)a[j_start + r];
                }
                int64_t min_gap_running = 0x7fffffffffffffffLL;
                int64_t lhs_running = 0;
                uint32_t pos_running = 0;

                for (uint32_t k_hor = j_start + s + 1; k_hor <= m; ++k_hor) {
                    uint32_t j_last = k_hor - s - 1;
                    int64_t gap_last = (int64_t)a[j_last + s] - (int64_t)a[j_last];
                    if (gap_last < min_gap_running) {
                        min_gap_running = gap_last;
                    }
                    int64_t w_last = ai - gap_last;
                    lhs_running += w_last;
                    if (w_last >= 1) pos_running += 1;

                    int64_t num_terms = (int64_t)(k_hor - s - j_start);
                    int64_t tail_sum = 0;
                    for (uint32_t r = 0; r < s; ++r) {
                        tail_sum += (int64_t)a[k_hor - s + r];
                    }
                    int64_t rhs = num_terms * ai + head_sum - tail_sum;
                    if (lhs_running != rhs) {
                        all_ok = 0;
                    }

                    uint32_t c_q_sid = d_quad_injection_count(rhs, m_sid);
                    if (c_q_sid > pos_running || pos_running > actual_pos) {
                        all_ok = 0;
                    }
                    if (c_q_sid > best_q_sid_win) {
                        best_q_sid_win = c_q_sid;
                    }

                    if (j_start == i) {
                        if (rhs > best_s_trunc) {
                            best_s_trunc = rhs;
                        }
                        uint32_t c_l_mg = (rhs > 0) ? (uint32_t)((rhs + m_mg - 1) / m_mg) : 0;
                        int64_t m_rg = ai - min_gap_running;
                        if (m_rg < 1) m_rg = 1;
                        uint32_t c_q_rg = d_quad_injection_count(rhs, m_rg);
                        if (!(c_l_mg <= c_q_sid && c_q_sid <= c_q_rg && c_q_rg <= pos_running)) {
                            all_ok = 0;
                        }
                        if (c_q_sid > best_q_sid_trunc) {
                            best_q_sid_trunc = c_q_sid;
                        }
                        if (c_q_rg > best_q_rg_trunc) {
                            best_q_rg_trunc = c_q_rg;
                        }
                    }
                }
            }

            if (best_q_sid_trunc > best_q_sid_win || best_q_sid_win > actual_pos) {
                all_ok = 0;
            }

            si_star += best_s_trunc;
            trunc_sid_tot += best_q_sid_trunc;
            win_sid_tot   += best_q_sid_win;
            trunc_rg_tot  += best_q_rg_trunc;

            int64_t c_qs_i64 = (int64_t)best_q_sid_trunc;
            if (c_qs_i64 > 0 && m_sid <= n_lt + c_evict) {
                c_evict += c_qs_i64;
                upper_w_sum += c_qs_i64 * m_sid - c_qs_i64 * (c_qs_i64 - 1) / 2;
            }
        }

        uint32_t ci_quad = d_quad_injection_count(si_star, (ai > 1) ? (ai - 1) : 1);
        double cap_lb = 0.5 * (1.0 + sqrt(1.0 + 8.0 * (double)si_star));
        if (ci_quad > ci_actual || (double)ai + 1e-9 < cap_lb || si_star > ai * (ai - 1) / 2) {
            all_ok = 0;
        }
        total_si_star += si_star;
    }

    int64_t poly_lhs = 0;
    for (uint32_t r_idx = 0; r_idx < m; ++r_idx) {
        int64_t r = (int64_t)(r_idx + 1);
        poly_lhs += (r * r - mf) * (int64_t)a[r_idx];
    }
    int64_t base_rhs = n_lt * (n_lt + 1) / 2;
    int64_t evict_rhs = (n_lt + c_evict) * (n_lt + c_evict + 1) / 2 - upper_w_sum;
    if (poly_lhs < evict_rhs || evict_rhs < base_rhs) {
        all_ok = 0;
    }

    out_all_ok[idx]            = all_ok;
    out_actual_pos[idx]        = actual_pos_tot;
    out_trunc_sidon_quad[idx]  = trunc_sid_tot;
    out_win_sidon_quad[idx]    = win_sid_tot;
    out_trunc_raygap_quad[idx] = trunc_rg_tot;
    out_total_si_star[idx]     = total_si_star;
    out_slot_evict_cnt[idx]    = (uint32_t)c_evict;
    out_poly_lhs[idx]          = poly_lhs;
    out_base_rhs[idx]          = base_rhs;
    out_evict_rhs[idx]         = evict_rhs;
}

__device__ __forceinline__ uint32_t d_min_dyadic_shell_from_x(uint32_t x) {
    if (x <= 2u) return 1u;
    uint32_t v = x - 1u;
    uint32_t ilog = 0u;
    while (v > 1u) {
        v >>= 1u;
        ilog += 1u;
    }
    return ilog + 1u;
}

__device__ __forceinline__ uint32_t d_min_dyadic_shell(int64_t w) {
    uint64_t abs_w = (w >= 0) ? (uint64_t)w : (uint64_t)(-w);
    if (abs_w == 0ULL) return 1u;
    uint64_t v = abs_w + 1ULL;
    uint32_t ilog = 0u;
    while (v > 1ULL) {
        v >>= 1ULL;
        ilog += 1u;
    }
    return ilog + 1u;
}

extern "C" __global__ void k_eval_b3_diophantine_haar_closure(
    const uint32_t* __restrict__ sets,              // [n_sets * max_m], 1-indexed sorted elements
    const uint32_t* __restrict__ lengths,           // [n_sets]
    uint32_t n_sets,
    uint32_t max_m,
    uint32_t r_max,                                 // dyadic shell horizon r_max <= 12
    uint32_t n_k,                                   // number of octave / period indices
    double k_star,                                  // \mathcal{K}_* = \mathrm{Vol}(\Omega_\infty^*)
    uint32_t* __restrict__ out_all_ok,              // [n_sets] 1 if Theorems 2.13 & 2.14(a)-(b) hold
    uint32_t* __restrict__ out_loc_triples,         // [n_sets] localized cross-shell triples
    double* __restrict__ out_act_excess,            // [n_sets] total_actual_subblock_excess
    double* __restrict__ out_lf_excess,             // [n_sets] total_lf_sawtooth_excess
    uint64_t* __restrict__ out_split_diff_sq,       // [n_sets] total_binary_split_diff_sq
    double* __restrict__ out_sawtooth_im,           // [n_k] I_m = \int_m^{m+1} (u-m)(m+1-u)/u du
    double* __restrict__ out_kappa_dio,             // [n_k] \kappa_{\mathrm{int},3}^{\mathrm{Dio}}(K)
    double* __restrict__ out_bound_dio,             // [n_k] c_{\infty,3}^{*,\mathrm{Dio}}(K)
    double* __restrict__ out_bound_dio_gk           // [n_k] c_{\infty,3}^{*,\mathrm{Dio,GK}}(K)
) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n_k) {
        uint64_t m = (uint64_t)idx;
        double im = 0.5;
        if (m > 0) {
            double mf = (double)m;
            im = mf + 0.5 - mf * (mf + 1.0) * log1p(1.0 / mf);
        }
        out_sawtooth_im[idx] = im;

        if (idx == 0) {
            double b0 = pow(k_star, -1.0 / 3.0);
            out_kappa_dio[idx]    = 0.0;
            out_bound_dio[idx]    = b0;
            out_bound_dio_gk[idx] = b0;
        } else {
            const double ln2 = 0.693147180559945309417232121458176568;
            const double c_gk = 0.4975089540675685;
            double kf = (double)idx;
            double four_neg_k = pow(4.0, -(double)idx);
            double two_neg_k  = pow(2.0, -(double)idx);
            double kappa_dio  = (kf * ln2) / (3.0 * (1.0 - four_neg_k));
            double bound_dio  = pow(k_star * (1.0 + kappa_dio), -1.0 / 3.0);
            double kappa_gk   = kappa_dio + (2.0 * c_gk) / (1.0 + two_neg_k);
            double bound_gk   = pow(k_star * (1.0 + kappa_gk), -1.0 / 3.0);
            out_kappa_dio[idx]    = kappa_dio;
            out_bound_dio[idx]    = bound_dio;
            out_bound_dio_gk[idx] = bound_gk;
        }
    }

    if (idx >= n_sets) return;

    uint32_t m_len = lengths[idx];
    const uint32_t* a = sets + idx * max_m;
    uint32_t horizon_n = 1u << r_max;

    uint32_t active[64];
    uint32_t n_act = 0;
    uint32_t shell_counts[16];
    for (uint32_t r = 0; r < 16; ++r) shell_counts[r] = 0;

    for (uint32_t i = 0; i < m_len && n_act < 64; ++i) {
        uint32_t x = a[i];
        if (x >= 1 && x <= horizon_n) {
            active[n_act++] = x;
            uint32_t r = d_min_dyadic_shell_from_x(x);
            if (r >= 1 && r <= r_max && r <= 15) {
                shell_counts[r] += 1;
            }
        }
    }

    uint32_t all_ok = 1;
    uint64_t p_pref = 0;
    for (uint32_t r = 1; r <= r_max && r <= 15; ++r) {
        uint64_t m = (uint64_t)shell_counts[r];
        uint64_t tot = p_pref + m;
        uint64_t lhs_cube = tot * tot * tot;
        uint64_t rhs_cube = p_pref * p_pref * p_pref + m * m * m
            + 3ULL * m * m * p_pref + 3ULL * m * p_pref * p_pref;
        uint64_t b3_tot  = (tot < 2) ? 0ULL : (tot * (tot - 1ULL) * (tot + 1ULL) / 6ULL);
        uint64_t b3_pref = (p_pref < 2) ? 0ULL : (p_pref * (p_pref - 1ULL) * (p_pref + 1ULL) / 6ULL);
        uint64_t b3_m    = (m < 2) ? 0ULL : (m * (m - 1ULL) * (m + 1ULL) / 6ULL);
        uint64_t b2_pref = p_pref * (p_pref + 1ULL) / 2ULL;
        uint64_t b2_m    = (m < 2) ? 0ULL : (m * (m - 1ULL) / 2ULL);
        if (lhs_cube != rhs_cube || (b3_tot - b3_pref) != (b3_m + m * b2_pref + p_pref * b2_m)) {
            all_ok = 0;
        }
        p_pref = tot;
    }

    uint32_t loc_triples = 0;
    for (uint32_t k = 1; k < n_act; ++k) {
        uint32_t ak = active[k];
        uint32_t r_k = d_min_dyadic_shell_from_x(ak);
        if (r_k >= 3) {
            uint32_t pow_rm2 = 1u << (r_k - 2);
            uint32_t pow_r   = 1u << r_k;
            for (uint32_t j = 0; j < k; ++j) {
                for (uint32_t i = 0; i <= j; ++i) {
                    uint32_t a_ij = active[i] + active[j];
                    if (a_ij <= pow_rm2) {
                        loc_triples += 1;
                        int64_t w = (int64_t)ak - (int64_t)a_ij;
                        uint32_t r_min = d_min_dyadic_shell(w);
                        if (!(w > (int64_t)pow_rm2 && w < (int64_t)pow_r && (r_min == r_k - 1 || r_min == r_k))) {
                            all_ok = 0;
                        }
                    }
                }
            }
        }
    }

    double total_act_ex = 0.0;
    double total_lf_ex  = 0.0;
    uint64_t total_diff_sq = 0;

    for (uint32_t r = 2; r <= r_max && r <= 12; ++r) {
        uint32_t shell_lo = 1u << (r - 1);
        uint32_t shell_hi = 1u << r;
        uint64_t s_count = (uint64_t)shell_counts[r];

        for (uint32_t d = 0; d < r; ++d) {
            uint32_t b_blocks = 1u << d;
            uint32_t w_width  = 1u << (r - 1 - d);
            uint64_t sum_pairs = 0;
            uint64_t sum_sq    = 0;

            for (uint32_t b_idx = 0; b_idx < b_blocks; ++b_idx) {
                uint32_t b_lo = shell_lo + b_idx * w_width;
                uint32_t b_hi = b_lo + w_width;
                uint64_t c = 0;
                for (uint32_t i = 0; i < n_act; ++i) {
                    uint32_t x = active[i];
                    if (x > b_lo && x <= b_hi && x <= shell_hi) {
                        c += 1;
                    }
                }
                if (c >= 2) sum_pairs += c * (c - 1ULL);
                sum_sq += c * c;

                if (d >= 1 && (b_idx & 1u) == 1u) {
                    uint32_t prev_lo = shell_lo + (b_idx - 1u) * w_width;
                    uint32_t prev_hi = prev_lo + w_width;
                    uint64_t u = 0;
                    for (uint32_t i = 0; i < n_act; ++i) {
                        uint32_t x = active[i];
                        if (x > prev_lo && x <= prev_hi && x <= shell_hi) {
                            u += 1;
                        }
                    }
                    uint64_t v = c;
                    uint64_t p_val = u + v;
                    uint64_t diff = (u >= v) ? (u - v) : (v - u);
                    if (2ULL * (u * u + v * v) != p_val * p_val + diff * diff) {
                        all_ok = 0;
                    }
                    total_diff_sq += diff * diff;
                }
            }

            uint64_t b_u64 = (uint64_t)b_blocks;
            uint64_t q = s_count / b_u64;
            uint64_t t = s_count % b_u64;
            uint64_t q_m1 = (q >= 1ULL) ? (q - 1ULL) : 0ULL;
            uint64_t lf_lb = b_u64 * q * q_m1 + 2ULL * q * t;
            uint64_t lhs_id = b_u64 * (b_u64 * q * q + 2ULL * q * t) + b_u64 * t;
            uint64_t rhs_id = s_count * s_count + t * (b_u64 - t);
            if (sum_pairs < lf_lb || lhs_id != rhs_id || 4ULL * t * (b_u64 - t) > b_u64 * b_u64) {
                all_ok = 0;
            }

            double bf = (double)b_blocks;
            double sf = (double)s_count;
            double tf = (double)t;
            double act_ex = (double)sum_sq - (sf * sf) / bf;
            double lf_ex  = tf * (bf - tf) / bf;
            if (act_ex + 1e-11 < lf_ex) {
                all_ok = 0;
            }
            total_act_ex += act_ex;
            total_lf_ex  += lf_ex;
        }
    }

    out_all_ok[idx]        = all_ok;
    out_loc_triples[idx]   = loc_triples;
    out_act_excess[idx]    = total_act_ex;
    out_lf_excess[idx]     = total_lf_ex;
    out_split_diff_sq[idx] = total_diff_sq;
}


