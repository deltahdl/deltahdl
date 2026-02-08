#include "elaboration/elaborator.h"

#include <algorithm>
#include <format>
#include <optional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaboration/const_eval.h"
#include "elaboration/rtlir.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"

namespace delta {

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  auto* mod_decl = FindModule(top_module_name);
  if (!mod_decl) {
    diag_.Error({}, std::format("top module '{}' not found", top_module_name));
    return nullptr;
  }

  auto* design = arena_.Create<RtlirDesign>();
  ParamList empty_params;
  auto* top = ElaborateModule(mod_decl, empty_params);
  if (!top) return nullptr;

  design->top_modules.push_back(top);
  design->all_modules[top->name] = top;
  return design;
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  auto it = std::find_if(unit_->modules.begin(), unit_->modules.end(),
                         [name](auto* mod) { return mod->name == name; });
  return (it != unit_->modules.end()) ? *it : nullptr;
}

static std::optional<int64_t> FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& [oname, oval] : params) {
    if (oname == name) {
      return oval;
    }
  }
  return std::nullopt;
}

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  auto* mod = arena_.Create<RtlirModule>();
  mod->name = decl->name;

  for (const auto& [pname, pval] : decl->params) {
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;

    auto override_val = FindParamOverride(params, pname);
    if (override_val) {
      pd.resolved_value = *override_val;
      pd.is_resolved = true;
    }
    if (!pd.is_resolved && pval) {
      pd.resolved_value = ConstEvalInt(pval).value_or(0);
      pd.is_resolved = ConstEvalInt(pval).has_value();
    }

    mod->params.push_back(pd);
  }

  ElaboratePorts(decl, mod);
  ElaborateItems(decl, mod);
  return mod;
}

// --- Port elaboration ---

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  for (const auto& port : decl->ports) {
    RtlirPort rp;
    rp.name = port.name;
    rp.direction = port.direction;
    rp.type_kind = port.data_type.kind;
    rp.width = EvalTypeWidth(port.data_type);
    rp.is_signed = port.data_type.is_signed;
    mod->ports.push_back(rp);
  }
}

// --- Module item elaboration ---

static RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
  switch (ak) {
    case AlwaysKind::kAlways:
      return RtlirProcessKind::kAlways;
    case AlwaysKind::kAlwaysComb:
      return RtlirProcessKind::kAlwaysComb;
    case AlwaysKind::kAlwaysFF:
      return RtlirProcessKind::kAlwaysFF;
    case AlwaysKind::kAlwaysLatch:
      return RtlirProcessKind::kAlwaysLatch;
  }
  return RtlirProcessKind::kAlwaysComb;
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kNetDecl: {
      RtlirNet net;
      net.name = item->name;
      net.net_type = NetType::kWire;
      net.width = EvalTypeWidth(item->data_type);
      mod->nets.push_back(net);
      break;
    }
    case ModuleItemKind::kVarDecl: {
      RtlirVariable var;
      var.name = item->name;
      var.width = EvalTypeWidth(item->data_type);
      var.is_4state = Is4stateType(item->data_type.kind);
      mod->variables.push_back(var);
      break;
    }
    case ModuleItemKind::kContAssign: {
      RtlirContAssign ca;
      ca.lhs = item->assign_lhs;
      ca.rhs = item->assign_rhs;
      mod->assigns.push_back(ca);
      break;
    }
    case ModuleItemKind::kInitialBlock: {
      RtlirProcess proc;
      proc.kind = RtlirProcessKind::kInitial;
      proc.body = item->body;
      mod->processes.push_back(proc);
      break;
    }
    case ModuleItemKind::kFinalBlock: {
      RtlirProcess proc;
      proc.kind = RtlirProcessKind::kFinal;
      proc.body = item->body;
      mod->processes.push_back(proc);
      break;
    }
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock: {
      RtlirProcess proc;
      proc.kind = MapAlwaysKind(item->always_kind);
      proc.body = item->body;
      proc.sensitivity = item->sensitivity;
      mod->processes.push_back(proc);
      break;
    }
    case ModuleItemKind::kModuleInst: {
      RtlirModuleInst inst;
      inst.module_name = item->inst_module;
      inst.inst_name = item->inst_name;
      inst.resolved = nullptr;
      mod->children.push_back(inst);
      break;
    }
    case ModuleItemKind::kParamDecl:
      break;
    case ModuleItemKind::kGenerateBlock:
      diag_.Warning(item->loc, "generate blocks are not yet elaborated");
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      mod->function_decls.push_back(item);
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  int64_t next_val = 0;
  for (const auto& member : item->typedef_type.enum_members) {
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }
    RtlirVariable var;
    var.name = member.name;
    var.width = EvalTypeWidth(item->typedef_type);
    var.is_4state = false;
    mod->variables.push_back(var);
    ++next_val;
  }
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }
}

}  // namespace delta
