#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/envelope_viewport.h"
#include "common/packed_range.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_decl_facts.h"
#include "simulator/vpi_frame_facts.h"
#include "simulator/vpi_instance_facts.h"
#include "simulator/vpi_user.h"

namespace delta {

struct AssocArrayObject;
struct ClassObject;
struct QueueObject;

struct VpiObject {
  int type = 0;
  std::string_view name;
  std::string full_name;
  Variable* var = nullptr;
  std::string run_key;
  bool value_change_watched = false;
  Net* net = nullptr;
  VpiObject* parent = nullptr;
  int direction = 0;
  int size = 0;
  int index = 0;

  bool default_clocking = false;
  bool global_clocking = false;

  int path_type = 0;
  int polarity = 0;
  int data_polarity = 0;
  int edge = 0;
  bool mod_path_has_if_none = false;
  int input_edge = 0;
  int output_edge = 0;
  VpiObject* input_skew = nullptr;
  VpiObject* output_skew = nullptr;

  bool data_path_term = false;

  int prim_type = 0;

  bool is_vectored = false;
  bool is_scalared = false;

  bool automatic = false;

  int alloc_scheme = kVpiOtherScheme;

  bool is_protected = false;
  ViewportAccess viewport_access = ViewportAccess::kNone;

  bool is_systf = false;

  bool is_assertion_cb = false;
  std::uint64_t assertion_cb_handle = 0;

  void* user_data = nullptr;

  bool scheduled = false;
  uint64_t event_time = 0;
  std::shared_ptr<bool> put_superseded;
  std::vector<VpiObject*> scheduled_puts;

  bool imported = false;
  bool in_compilation_unit = false;

  bool implicit_decl = false;

  int time_precision = 0;

  int time_unit = 0;

  uint64_t time_queue_time = 0;

  bool has_scheduled_time = false;

  std::string library_name;
  std::string cell_name;
  std::string config_name;
  VpiInstanceFacts instance_facts;

  std::string def_name;

  int op_type = 0;

  int const_type = 0;

  int indexed_part_select_type = 0;

  int bit_offset = -1;

  std::vector<PackedRange> packed_dims;

  std::optional<PackedRange> select_dim;
  int select_base_offset = 0;

  VpiObject* left_range = nullptr;
  VpiObject* right_range = nullptr;
  VpiObject* base_expr = nullptr;
  VpiObject* width_expr = nullptr;

  bool op_strong = false;

  bool cover_sequence = false;

  bool clock_inferred = false;

  bool is_deferred = false;
  bool is_final = false;

  bool active = false;

  std::string file;
  int start_line = 0;
  int column = 0;
  int end_line = 0;
  int end_column = 0;

  int line_no = 0;

  bool def_attribute = false;
  std::string def_file;
  int def_line_no = 0;

  std::vector<VpiDelayInfo> delays;

  VpiObject* delay_expr = nullptr;

  VpiObject* high_conn = nullptr;
  VpiObject* low_conn = nullptr;

  VpiObject* actual = nullptr;

  VpiObject* io_expr = nullptr;

  VpiObject* prefix = nullptr;

  int actual_origin = kVpiActualBySimTime;

  int port_type = 0;

  bool explicit_name = false;

  bool null_port = false;

  bool generic_interface = false;

  bool is_modport = false;

  int case_type = 0;

  int qualifier = 0;

  bool default_case_item = false;

  int always_type = 0;
  VpiObject* body = nullptr;
  VpiObject* process = nullptr;
  VpiObject* else_stmt = nullptr;
  VpiObject* clocking_event = nullptr;
  VpiObject* disable_condition = nullptr;

  bool blocking = false;

  int join_type = 0;

  bool local_var_decls = false;

  bool array_member = false;

  VpiObject* index_expr = nullptr;
  std::shared_ptr<const struct VpiExprScope> expr_scope;

  int array_type = 0;

  bool decl_signed = false;
  bool decl_scalar = false;
  bool decl_vector = false;

  QueueObject* queue = nullptr;
  AssocArrayObject* assoc = nullptr;

  QueueObject* element_of_queue = nullptr;
  AssocArrayObject* element_of_assoc = nullptr;

  VpiObject* member_of = nullptr;
  uint32_t member_offset = 0;

  ClassObject* property_of = nullptr;

  std::vector<std::vector<int>> array_dim_indices;

  bool top_module = false;

  int def_decay_time = 0;

  VpiObject* tf_prefix = nullptr;
  std::vector<std::string_view> prefix_members;

  VpiObject* tf_decl = nullptr;
  VpiObject* property_decl = nullptr;
  VpiObject* sequence_decl = nullptr;
  VpiObject* udp_defn = nullptr;

  VpiObject* disable_target = nullptr;

  VpiObject* tf_with = nullptr;
  bool tf_with_method = false;

  bool builtin_method = false;

  int func_type = 0;

  bool user_defined = false;

  std::string decompile;

  VpiObject* user_systf = nullptr;

  std::vector<VpiObject*> arguments;

  std::vector<VpiObject*> written_arguments;

  bool written_as_stmt = false;

  int offset = 0;

  bool net_decl_assign = false;

  int strength0 = 0;
  int strength1 = 0;

  int access_type = 0;

  bool is_virtual = false;

  bool constraint_enabled = false;

  int dist_type = 0;

  bool packed = false;
  bool tagged = false;
  bool soft = false;

  bool local_param = false;
  bool conn_by_name = false;
  VpiObject* param_default = nullptr;
  VpiObject* param_typespec = nullptr;
  bool explicit_param_range = false;
  VpiObject* param_left_range = nullptr;
  VpiObject* param_right_range = nullptr;

  bool implicit_builtin_method = false;

  bool inline_constraint = false;

  std::vector<VpiObject*> derived_classes;
  std::vector<VpiObject*> specializations;

  VpiDeclFacts decl_facts;
  VpiFrameFacts frame_facts;

  int64_t obj_id = 0;

  VpiObject* referenced_object = nullptr;

  VpiObject* tchk_ref_term = nullptr;
  VpiObject* tchk_data_term = nullptr;
  VpiObject* term_expr = nullptr;
  VpiObject* written_condition = nullptr;
  std::vector<VpiObject*> tchk_arguments;

  int tchk_type = 0;

  VpiObject* tchk_notifier = nullptr;

  VpiObject* in_term = nullptr;
  VpiObject* out_term = nullptr;
  VpiObject* term_net = nullptr;
  VpiObject* delay_source = nullptr;

  VpiObject* lhs = nullptr;
  VpiObject* rhs = nullptr;

  int delay_type = 0;

  VpiObject* foreach_array = nullptr;

  std::vector<VpiObject*> loop_vars;

  VpiObject* callback = nullptr;

  std::vector<VpiObject*> for_init_stmts;
  std::vector<VpiObject*> for_inc_stmts;

  std::vector<VpiObject*> constraint_exprs;
  std::vector<VpiObject*> else_constraint_exprs;
  std::vector<VpiObject*> solve_before;
  std::vector<VpiObject*> solve_after;
  VpiObject* value_range = nullptr;
  VpiObject* weight = nullptr;
  ClassObject* constraint_of = nullptr;

  VpiObject* return_var = nullptr;

  bool is_dpi = false;
  bool dpi_export = false;
  bool dpi_pure = false;
  bool dpi_context = false;
  bool is_dpi_c = false;
  std::string dpi_c_identifier;

  std::vector<VpiObject*> children;
  size_t scan_index = 0;

  VpiObject* iter_ref = nullptr;

  int iter_type = 0;

  VpiObject* same_object_as = nullptr;

  bool object_exists = true;

  bool released = false;

  int handles_held = 0;

  bool has_side_effects = false;

  int side_effect_count = 0;

  bool property_needs_side_effect_eval = false;

  std::vector<VpiObject*> index_expressions;

  VpiObject* aliased = nullptr;

  VpiObject* inner_typespec = nullptr;
  int rand_type = 0;

  VpiObject* nettype_with = nullptr;
};

inline bool VpiReadSealed(const VpiObject& obj) {
  return obj.is_protected && obj.viewport_access == ViewportAccess::kNone;
}

inline bool VpiWriteSealed(const VpiObject& obj) {
  return obj.is_protected && obj.viewport_access != ViewportAccess::kReadWrite;
}

using VpiHandle = VpiObject*;

inline vpiHandle VpiHandleOf(VpiObject* object) {
  return reinterpret_cast<vpiHandle>(object);
}

inline VpiObject* VpiObjectOf(vpiHandle handle) {
  return reinterpret_cast<VpiObject*>(handle);
}

}  // namespace delta
