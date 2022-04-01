(benchmark test
:extrafuns ((cont1_1 BitVec[32]))
:extrafuns ((cont_1 BitVec[32]))
:extrafuns ((cont_2 BitVec[32]))
:extrafuns ((r_in_1 BitVec[32]))
:extrafuns ((r_in_2 BitVec[32]))
:extrafuns ((stato_1 BitVec[32]))
:extrafuns ((stato_2 BitVec[32]))

:exists( cont1_1 cont_1 cont_2 r_in_1 r_in_2 stato_1 stato_2)

:formula (exists (cont1_1 BitVec[32]) (cont_1 BitVec[32]) (cont_2 BitVec[32]) (r_in_1 BitVec[32]) (r_in_2 BitVec[32]) (stato_1 BitVec[32]) (stato_2 BitVec[32])   (and (and (and (and (and (and (and (and (= (bvmul bv1[32] cont_1 ) bv0[32] ) (bvuge cont_2 bv38[32] ) ) (= (bvmul bv1[32] stato_2 ) bv2[32] ) ) (not (= (bvmul bv1[32] stato_2 ) bv1[32] )) ) (= (bvadd (bvmul bv1[32] cont1_1 ) (bvmul bv255[32] r_in_2 ) ) bv0[32] ) ) (= (bvmul bv1[32] r_in_2 ) bv0[32] ) ) (= (bvmul bv1[32] stato_1 ) bv8[32] ) ) (= (bvadd (bvmul bv1[32] r_in_1 ) (bvmul bv255[32] r_in_2 ) ) bv0[32] ) ) (not (= (bvmul bv1[32] stato_2 ) bv0[32] )) ) )
)
