import tactic.core

namespace tactic
setup_tactic_parser
namespace interactive

meta def sim (use_assumption_discharger : parse $ (tk "@")?) (use_iota_eqn : parse $ (tk "!")?) (trace_lemmas : parse $ (tk "?")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let iota_cfg : parse (tk "!")? → simp_config_ext → simp_config_ext := λ param cfg, option.elim param cfg (λ _, {iota_eqn := tt, .. cfg} ) in
let trace_cfg : parse (tk "?")? → simp_config_ext → simp_config_ext := λ param cfg, option.elim param cfg (λ _, {trace_lemmas := tt, .. cfg} ) in
let assumption_discharger_cfg : parse (tk "@")? → simp_config_ext → simp_config_ext := λ param cfg, option.elim param cfg (λ _, {discharger := tactic.assumption, .. cfg} ) in
let cfg := iota_cfg use_iota_eqn (trace_cfg trace_lemmas (assumption_discharger_cfg use_assumption_discharger cfg))
in
propagate_tags $
do lms ← simp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat,
  if cfg.trace_lemmas then trace (↑"Try this: simp only " ++ to_fmt lms.to_list) else skip

end interactive
end tactic
