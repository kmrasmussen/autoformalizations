import PolicyGradient.Proofs.ResidAsm
open PolicyGradient PolicyGradient.Proofs
-- Confirm: the frozen goal, IF proved, closes AKM 5.1 via the existing bridge.
#check @Proofs.limitAdvNonpos_of_offsupport
#check @Proofs.tendsto_vstar_of_limitAdvNonpos
#check @Proofs.vinf_eq_vstar_of_adv_nonpos
