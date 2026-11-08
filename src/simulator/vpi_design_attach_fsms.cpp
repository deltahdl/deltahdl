#include "simulator/vpi_design_attach_fsms.h"

#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "elaborator/rtlir.h"
#include "parser/ast_fsm.h"
#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiObject* ChildObject(VpiObject* parent, int type, std::string_view name,
                       const VpiAttachBuild& build) {
  VpiObject* child = build.alloc();
  child->type = type;
  child->name = build.keep(std::string(name));
  child->full_name = parent->full_name + "." + std::string(name);
  child->parent = parent;
  parent->children.push_back(child);
  return child;
}

VpiObject* StateExpression(const FsmDecl& decl, VpiObject* scope,
                           const VpiAttachBuild& build) {
  if (decl.state_signals.size() > 1) {
    VpiObject* concat = build.alloc();
    concat->type = vpiOperation;
    concat->op_type = vpiConcatOp;
    for (std::string_view name : decl.state_signals) {
      concat->children.push_back(ChildNamed(scope, name));
    }
    return concat;
  }
  VpiObject* signal = ChildNamed(scope, decl.state_signals.front());
  if (!decl.has_part_select) return signal;
  VpiObject* select = build.alloc();
  select->type = vpiPartSelect;
  select->name = signal->name;
  select->parent = signal;
  select->left_range = VpiIntConstant(decl.msb, build);
  select->right_range = VpiIntConstant(decl.lsb, build);
  return select;
}

void AttachFsmStates(VpiObject* fsm, InstanceFsms& inst, std::size_t index,
                     SimContext& ctx, const VpiAttachBuild& build) {
  CodeCoverage& code = ctx.GetCoverageControlState().Code();
  for (const auto& [state_name, value] : inst.fsms[index].states) {
    VpiObject* state = ChildObject(fsm, vpiFsmHandle, state_name, build);
    state->var = ctx.FindVariable(VpiFlatName(inst.prefix, state_name));
    state->size = static_cast<int>(state->var->value.width);
    code.fsm_handles[state] = {&inst, index, value, nullptr};
  }
}

void AttachInstanceFsms(InstanceFsms& inst, VpiObject* scope, SimContext& ctx,
                        const VpiAttachBuild& build) {
  CodeCoverage& code = ctx.GetCoverageControlState().Code();
  for (std::size_t i = 0; i < inst.fsms.size(); ++i) {
    const FsmCount& count = inst.fsms[i];
    const std::string_view kName = count.decl.fsm_name.empty()
                                       ? count.decl.state_signals.front()
                                       : count.decl.fsm_name;
    VpiObject* fsm = ChildObject(scope, vpiFsm, kName, build);
    code.fsm_handles[fsm] = {&inst, i, std::nullopt,
                             StateExpression(count.decl, scope, build)};
    AttachFsmStates(fsm, inst, i, ctx, build);
  }
}

}  // namespace

void AttachFsms(const RtlirDesign* design, const VpiObjectMap& objects,
                SimContext& ctx, const VpiAttachBuild& build) {
  std::unordered_map<std::string_view, InstanceFsms*> by_prefix;
  for (InstanceFsms& inst :
       ctx.GetCoverageControlState().Code().fsm_instances) {
    by_prefix.emplace(inst.prefix, &inst);
  }
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule*, const std::string& prefix, VpiHandle scope) {
        auto found = by_prefix.find(prefix);
        if (found != by_prefix.end()) {
          AttachInstanceFsms(*found->second, scope, ctx, build);
        }
      });
}

}  // namespace delta
