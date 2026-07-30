#pragma once

#include <cstdint>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

class Arena;
class DiagEngine;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
struct RtlirModuleInst;
struct RtlirParamDecl;

// The elaborator's state, held apart from the methods that act on it so that
// neither half outgrows the file line cap on its own. Elaborator derives from
// this, so every member is reached unqualified exactly as before and no
// definition needed rewriting; the members are protected rather than private
// for that reason.
class ElaboratorData {
 public:
  // §7.4.2 writes an unpacked dimension either as a constant_range — two
  // bounds, in the order the declaration chose — or as a single size, which
  // stands for the range [0:size-1]. Both bounds are kept rather than just the
  // lower one, because the order they were written in is the order a range over
  // that dimension has to be written in: §11.5.1 requires the first index of a
  // range to address a more significant element than the second, and which of
  // the two bounds is the more significant one is exactly what a lone size or a
  // lone minimum cannot say.
  struct DeclaredDim {
    int64_t left = 0;
    int64_t right = 0;

    // §11.5.1: a dimension written with its larger bound first counts downward,
    // so the more significant element is the one with the larger index. Bounds
    // that are equal describe a single element, which reads either way.
    [[nodiscard]] bool IsDescending() const { return left >= right; }
  };

  struct VarArrayInfo {
    DataTypeKind elem_type = DataTypeKind::kImplicit;
    uint32_t unpacked_size = 0;
    uint32_t num_unpacked_dims = 0;
    uint32_t elem_width = 0;
    bool elem_is_signed = false;
    bool elem_is_4state = true;
    bool is_dynamic = false;
    bool is_assoc = false;
    std::string_view assoc_index_type;
    std::vector<uint32_t> dim_sizes;
    // One entry per unpacked dimension whose bounds fold to constants, in
    // declaration order. A dimension whose bounds do not fold contributes
    // nothing, so a vector shorter than num_unpacked_dims does not line up with
    // the declaration and cannot be indexed by dimension.
    std::vector<DeclaredDim> declared_dims;
    bool is_queue = false;
  };

 protected:
  friend struct ItemElaborationStateSaver;  // per-module state save/restore

  // §23.9/§24.3: stack of enclosing lexical scopes' visible names. A lexically
  // nested module/program/interface sees names declared in the modules that
  // textually enclose it; ElaborateModule pushes one entry per enclosing scope
  // around a nested declaration's elaboration. A separately-instantiated module
  // breaks the lexical chain, so its elaboration starts from an empty stack.
  std::vector<std::unordered_set<std::string_view>> enclosing_scope_names_;
  std::unordered_set<std::string_view> pending_enclosing_scope_;
  bool has_pending_enclosing_scope_ = false;

  std::unordered_set<std::string_view> declared_names_;
  // §27.4: genvar names of the loop generate constructs currently being
  // elaborated. Used to reject a nested loop generate construct that reuses an
  // enclosing loop's genvar, which is illegal because the inner reference names
  // the outer block's implicit localparam rather than a genvar.
  std::unordered_set<std::string_view> active_loop_genvars_;
  std::unordered_set<std::string_view> net_names_;
  std::unordered_map<std::string_view, SourceLoc> cont_assign_targets_;
  std::unordered_map<std::string_view, SourceLoc> proc_assign_targets_;
  std::unordered_map<std::string_view, DataTypeKind> var_types_;
  std::unordered_map<std::string_view, VarArrayInfo> var_array_info_;
  std::unordered_map<std::string_view, const ModuleItem*> dpi_import_decls_;

  std::unordered_set<std::string_view> packed_array_vars_;
  std::unordered_set<std::string_view> specparam_names_;
  std::unordered_set<std::string_view> enum_var_names_;
  std::unordered_set<std::string_view> enum_member_names_;
  std::unordered_set<std::string_view> const_names_;
  // §6.19: const *variables* only (not parameters/specparams), which unlike
  // elaboration-time constants may not appear in an enum named-constant value.
  std::unordered_set<std::string_view> const_var_names_;

  std::unordered_map<std::string_view, DataTypeKind> forward_typedef_kinds_;
  std::unordered_set<std::string_view> class_names_;
  std::unordered_set<std::string_view> parameterized_class_names_;
  std::unordered_set<std::string_view> class_var_names_;
  std::unordered_map<std::string_view, std::string_view> class_var_types_;
  std::unordered_set<std::string_view> var_init_names_;
  std::unordered_map<std::string_view, SourceLoc> output_port_targets_;
  std::unordered_set<std::string_view> nettype_net_names_;
  std::unordered_set<std::string_view> nettype_names_;
  std::unordered_map<std::string_view, std::string_view> nettype_resolve_funcs_;
  std::unordered_map<std::string_view, std::string_view> nettype_canonical_;
  std::unordered_set<std::string_view> interconnect_names_;
  std::unordered_set<std::string_view> scalar_var_names_;
  std::unordered_set<std::string_view> task_names_;
  std::unordered_set<std::string_view> let_names_;  // §11.12 let decl names
  std::unordered_set<std::string_view> sequence_names_;
  // §16.12/§F.4.1: property+sequence registry to flatten an instance body.
  PropertyRegistry property_registry_;

  std::unordered_map<std::string_view, const ModuleItem*> func_decls_;
  std::unordered_map<std::string_view, std::string_view> var_named_types_;
  std::set<std::pair<std::string_view, std::string_view>> alias_pairs_;
  // §10.11: flag a bit-level alias correspondence specified more than once
  // across statements. AliasBitRef = (raw net name, bit index).
  using AliasBitRef = std::pair<std::string_view, uint32_t>;
  std::set<std::pair<AliasBitRef, AliasBitRef>> alias_bit_pairs_;

  std::unordered_set<std::string_view> non_ansi_complete_ports_;
  std::unordered_map<std::string_view, uint32_t> non_ansi_partial_ports_;
  // Non-ANSI partial ports whose port direction declaration carried `signed`.
  std::unordered_set<std::string_view> non_ansi_signed_ports_;

  std::unordered_set<std::string_view> ansi_port_names_;

  std::unordered_map<std::string_view, std::string_view> interface_inst_types_;
  std::unordered_map<std::string_view, std::string_view>
      vi_var_interface_types_;
  std::unordered_map<std::string_view, std::string_view> vi_var_modports_;

  // §25.9: explicit parameter value overrides, evaluated to constants, for
  // virtual interface variables and for interface instances. Used to verify
  // that the actual parameter values match for a virtual interface and the
  // interface (instance or other virtual interface) it is assigned from.
  std::unordered_map<std::string_view, std::vector<int64_t>>
      vi_var_param_values_;
  std::unordered_map<std::string_view, std::vector<int64_t>>
      interface_inst_param_values_;
  // §25.9: interface instances targeted by a defparam declared outside the
  // interface; such an instance shall not be assigned to a virtual interface.
  std::unordered_set<std::string_view> vi_external_defparam_insts_;

  std::unordered_set<std::string_view> checker_inst_names_;
  std::unordered_set<std::string_view> program_inst_names_;
  std::unordered_set<std::string_view> auto_task_func_names_;
  std::unordered_map<std::string_view, ModuleDecl*> nested_module_decls_;

  std::unordered_map<std::string_view, std::unordered_set<std::string_view>>
      pkg_provided_names_;

  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>
      explicit_imports_;

  std::vector<std::string_view> wildcard_packages_;

  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed_;

  struct ClockingSignalInfo {
    Direction direction;
  };
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, ClockingSignalInfo>>
      clocking_signals_;

  // §14.14: true while elaborating a module (or checker/interface/program)
  // whose own scope, or some enclosing ancestor instance up to the top-level
  // hierarchy block, declares a global clocking. A $global_clock reference is
  // legal when this is set; the flag implements the hierarchical lookup (rule
  // b) that climbs the instance tree. Saved and restored around each
  // ElaborateModule call so it tracks the ancestor chain of the current cell.
  bool global_clocking_in_scope_ = false;

  struct PendingGenerate {
    ModuleItem* item;
    RtlirModule* mod;
  };
  std::vector<PendingGenerate> pending_generates_;

  std::set<std::tuple<RtlirModule*, const ModuleItem*, size_t>>
      applied_defparams_;

  struct EarlyDefparamResolution {
    RtlirModule* root;
    const Expr* path_expr;
    RtlirParamDecl* resolved;
    SourceLoc loc;
  };
  std::vector<EarlyDefparamResolution> early_defparam_resolutions_;
};

}  // namespace delta
