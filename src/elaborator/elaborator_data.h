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

// How many times a loop generate scheme may iterate before elaboration stops
// and reports, unless a caller sets another bound with
// Elaborator::SetMaxGenerateIterations.
//
// §27.4 states no such bound. Its four error rules are a generate block
// instance array name conflicting with another declaration, a scheme that does
// not terminate, a repeated genvar value and a genvar bit set to x or z, so
// this is a budget of this elaborator's rather than a rule of the standard.
//
// The budget is what stands between a scheme that never terminates and an
// elaboration that never returns. The genvar-repeats check catches a scheme
// that revisits a value, which is the shape that can be proven
// non-terminating. What reaches this bound has a distinct genvar value every
// time round, which §27.4 permits outright -- "This can be a sparse array
// because the genvar values do not have to form a contiguous range of
// integers" -- so it cannot be told apart from a scheme that would have
// stopped one iteration later.
//
// 262144 is measured rather than chosen, and the measurement is recorded here
// so that questioning the number does not mean retaking it. A scheme reaching
// 65536 iterations costs 0.69 s, measured as
// GenerateElaboration.GenerateForNonTerminatingLoopErrors in
// unit-test-coverage-shard-03 of run 31852899070, which is 10.5 us an
// iteration. 262144 therefore costs under 3 s in the worst case, where a
// scheme really does not terminate, and it clears the largest design the
// budget has to admit by a factor of two: a per-bit generate over a 128Ki-entry
// memory is 131072 iterations. A design needing more asks for it with
// --max-generate-iterations, which is what makes this a budget and not a limit.
inline constexpr int64_t kDefaultMaxGenerateIterations = 262144;

// The elaborator's state, held apart from the methods that act on it so that
// neither half outgrows the file line cap on its own. Elaborator derives from
// this, so every member is reached unqualified exactly as before and no
// definition needed rewriting; the members are protected rather than private
// for that reason.
class ElaboratorData {
 public:
  // The two types below are public so free helpers (e.g. FormalArrayInfo in
  // elaborator_validate_class_array_*.cpp) can name and build them.
  //
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

  std::unordered_map<std::string_view, const ModuleItem*>
      deferred_subroutine_map_;

  std::string gen_prefix_;

  // §20.10.1: the constant bindings (genvars, and any localparams introduced
  // by the enclosing generate blocks) in effect while a generate body is being
  // elaborated. An elaboration severity task's argument list may reference a
  // genvar (see §20.10.1 Example 2, `$info("i = %0d ...", i)`), which is a
  // constant expression per §11.2.1 but is absent from BuildParamScope. This
  // overlay makes those bindings visible to the constant-argument check. Empty
  // outside any generate construct.
  ScopeMap gen_const_scope_;

  // §27.4: the implicit localparam of each loop generate block currently being
  // unrolled, outermost first, paired with this instance's loop-index value.
  // Stamped onto every process elaborated inside the block so that the value
  // survives to simulation, where the shared body AST can no longer tell the
  // instances apart. Empty outside a loop generate construct.
  std::vector<std::pair<std::string_view, int64_t>> gen_loop_consts_;

  // §20.10.1: any $fatal or $error elaboration severity task that survives
  // generate-construct expansion sets this to true. Propagated onto the
  // resulting RtlirDesign so the simulator can refuse to start.
  bool elab_simulation_blocked_ = false;

  // §20.10.1: details of the most recent elaboration severity task call.
  // Propagated onto the RtlirDesign so observers can inspect what was
  // emitted (severity tag, source location, hierarchical scope, user text).
  std::string elab_last_severity_;
  std::string elab_last_severity_msg_;
  std::string elab_last_severity_scope_;
  SourceLoc elab_last_severity_loc_;

  std::vector<std::string> library_order_;

  bool library_order_strict_ = false;

  int64_t max_generate_iterations_ = kDefaultMaxGenerateIterations;

  // A cell selection clause paired with a use expansion clause (§33.4.1.4,
  // §33.4.1.6). src_lib is the library qualifying the selected cell, empty when
  // the clause is unqualified and so applies to the cell in any library.
  // use_lib/use_cell name the binding target; an empty use_lib means the
  // library is inherited from the parent cell.
  struct CellUseOverride {
    std::string src_lib;
    std::string use_lib;
    std::string use_cell;
  };
  std::unordered_map<std::string, CellUseOverride> cell_clause_use_overrides_;

  // A cell selection clause paired with a liblist expansion clause: the named
  // cell is searched for in this ordered library list (§33.4.1.4, §33.4.1.5).
  std::unordered_map<std::string, std::vector<std::string>>
      cell_clause_liblist_overrides_;

  std::vector<std::pair<std::string, std::vector<std::string>>>
      instance_liblist_overrides_;

  std::vector<std::tuple<std::string, std::string, std::string>>
      instance_use_overrides_;

  // An instance selection clause paired with a plain use expansion clause
  // (§33.4.1.6): the exact instance at inst_path is bound to use_lib.use_cell.
  // Kept separate from instance_use_overrides_ (which carries the config
  // delegation of a use ...:config clause) so delegation is unaffected. An
  // empty use_lib means the target library is inherited from the parent cell.
  std::vector<std::tuple<std::string, std::string, std::string>>
      instance_bind_overrides_;

  // A configuration's parameter overrides for one instance path (§33.4.3).
  // reset_all marks an empty "#()" list that returns every parameter to its
  // module default; within params, a null expression returns that single
  // parameter to its default while a present expression supplies a new value.
  struct ConfigParamOverride {
    std::string inst_path;
    bool reset_all = false;
    std::vector<std::pair<std::string_view, Expr*>> params;
  };
  std::vector<ConfigParamOverride> instance_param_overrides_;

  // Literal values of the localparams declared in the configuration being
  // elaborated, used to evaluate parameter-override expressions (§33.4.3).
  ScopeMap config_localparam_scope_;

  std::string current_inst_path_;
  // Library of the cell currently being elaborated; the parent cell's library
  // while its child instances are resolved (§33.4.1.5, §33.4.1.6).
  std::string current_library_;
  // True while elaborating from a configuration, so config-specific library
  // resolution rules apply (§33.4.1.5).
  bool in_config_elaboration_ = false;

  TypedefMap typedefs_;
  // §6.24.3: names of typedefs whose unpacked dimensions designate an
  // associative array. A bit-stream cast must reject any such typedef as a
  // destination type.
  std::unordered_set<std::string_view> assoc_typedef_names_;
  // §6.24.3: total bit width of a typedef whose unpacked dimensions are all
  // fixed-size (no dynamic, queue, or associative dims). Used to detect
  // fixed-size mismatch when the destination of a bit-stream cast is an
  // unpacked-array typedef.
  std::unordered_map<std::string_view, uint32_t> fixed_unpacked_typedef_widths_;
  std::unordered_map<std::string_view, std::vector<Expr*>> td_array_dims_;
  std::unordered_set<std::string_view> cu_scope_names_;
  ScopeMap cu_param_scope_;

  // §11.4.12.1: the replication-multiplier checks (non-negative, zero-only-
  // within-a-concatenation) evaluate the multiplier as a constant expression.
  // The clause's own examples use a parameter multiplier, so the checks must
  // resolve parameters/localparams rather than only literals. This holds the
  // parameter scope of the module currently under constraint validation.
  ScopeMap replicate_multiplier_scope_;

  // §11.4.14.2: a streaming slice_size written as a constant expression may be
  // a parameter or localparam (a §11.2.1 constant form), so the zero/negative
  // slice-size check must fold it in the module's parameter scope rather than
  // an empty one. Holds the parameter scope of the module currently under
  // constraint validation, published alongside replicate_multiplier_scope_.
  ScopeMap streaming_slice_size_scope_;

  // §20.7.1/§20.7: the dimension argument n of an array query function is a
  // constant expression, so it may be a parameter, localparam, or genvar (a
  // §11.2.1 constant form) rather than only an integer literal. The
  // variable-sized-dimension check folds n in the module's parameter scope so a
  // parameter-valued dimension index is recognized the same way a literal one
  // is. Holds the parameter scope of the module currently under constraint
  // validation.
  ScopeMap array_query_dim_scope_;

  // §20.16.3: the ascending-order requirement on a PLA memory or term is tested
  // against its declared packed and unpacked ranges. Those range bounds are
  // §11.2.1 constant expressions, so they may be a parameter or localparam
  // rather than an integer literal (the LRM's own example declares the memory
  // with symbolic bounds). The check folds each bound in the module's parameter
  // scope so a parameter-valued bound resolves the same way a literal one does.
  ScopeMap pla_ascending_scope_;
};

}  // namespace delta
