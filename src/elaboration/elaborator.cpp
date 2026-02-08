#include "elaboration/elaborator.h"

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaboration/const_eval.h"
#include "elaboration/rtlir.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"

#include <format>
#include <optional>

namespace delta {

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

RtlirDesign* Elaborator::elaborate(std::string_view top_module_name) {
    auto* mod_decl = find_module(top_module_name);
    if (!mod_decl) {
        diag_.error({}, std::format("top module '{}' not found", top_module_name));
        return nullptr;
    }

    auto* design = arena_.create<RtlirDesign>();
    ParamList empty_params;
    auto* top = elaborate_module(mod_decl, empty_params);
    if (!top)
        return nullptr;

    design->top_modules.push_back(top);
    design->all_modules[top->name] = top;
    return design;
}

ModuleDecl* Elaborator::find_module(std::string_view name) const {
    for (auto* mod : unit_->modules) {
        if (mod->name == name)
            return mod;
    }
    return nullptr;
}

static std::optional<int64_t> find_param_override(const Elaborator::ParamList& params,
                                                  std::string_view name) {
    for (const auto& [oname, oval] : params) {
        if (oname == name) {
            return oval;
        }
    }
    return std::nullopt;
}

RtlirModule* Elaborator::elaborate_module(ModuleDecl* decl, const ParamList& params) {
    auto* mod = arena_.create<RtlirModule>();
    mod->name = decl->name;

    for (const auto& [pname, pval] : decl->params) {
        RtlirParamDecl pd;
        pd.name = pname;
        pd.default_value = pval;
        pd.is_resolved = false;

        auto override_val = find_param_override(params, pname);
        if (override_val) {
            pd.resolved_value = *override_val;
            pd.is_resolved = true;
        }
        if (!pd.is_resolved && pval) {
            pd.resolved_value = const_eval_int(pval).value_or(0);
            pd.is_resolved = const_eval_int(pval).has_value();
        }

        mod->params.push_back(pd);
    }

    elaborate_ports(decl, mod);
    elaborate_items(decl, mod);
    return mod;
}

// --- Port elaboration ---

void Elaborator::elaborate_ports(ModuleDecl* decl, RtlirModule* mod) {
    for (const auto& port : decl->ports) {
        RtlirPort rp;
        rp.name = port.name;
        rp.direction = port.direction;
        rp.type_kind = port.data_type.kind;
        rp.width = eval_type_width(port.data_type);
        rp.is_signed = port.data_type.is_signed;
        mod->ports.push_back(rp);
    }
}

// --- Module item elaboration ---

static ProcessKind map_always_kind(AlwaysKind ak) {
    switch (ak) {
    case AlwaysKind::Always:
        return ProcessKind::AlwaysComb;
    case AlwaysKind::AlwaysComb:
        return ProcessKind::AlwaysComb;
    case AlwaysKind::AlwaysFF:
        return ProcessKind::AlwaysFF;
    case AlwaysKind::AlwaysLatch:
        return ProcessKind::AlwaysLatch;
    }
    return ProcessKind::AlwaysComb;
}

void Elaborator::elaborate_item(ModuleItem* item, RtlirModule* mod) {
    switch (item->kind) {
    case ModuleItemKind::NetDecl: {
        RtlirNet net;
        net.name = item->name;
        net.net_type = NetType::Wire;
        net.width = eval_type_width(item->data_type);
        mod->nets.push_back(net);
        break;
    }
    case ModuleItemKind::VarDecl: {
        RtlirVariable var;
        var.name = item->name;
        var.width = eval_type_width(item->data_type);
        var.is_4state = is_4state_type(item->data_type.kind);
        mod->variables.push_back(var);
        break;
    }
    case ModuleItemKind::ContAssign: {
        RtlirContAssign ca;
        ca.lhs = item->assign_lhs;
        ca.rhs = item->assign_rhs;
        mod->assigns.push_back(ca);
        break;
    }
    case ModuleItemKind::InitialBlock: {
        RtlirProcess proc;
        proc.kind = ProcessKind::Initial;
        proc.body = item->body;
        mod->processes.push_back(proc);
        break;
    }
    case ModuleItemKind::FinalBlock: {
        RtlirProcess proc;
        proc.kind = ProcessKind::Final;
        proc.body = item->body;
        mod->processes.push_back(proc);
        break;
    }
    case ModuleItemKind::AlwaysBlock:
    case ModuleItemKind::AlwaysCombBlock:
    case ModuleItemKind::AlwaysFFBlock:
    case ModuleItemKind::AlwaysLatchBlock: {
        RtlirProcess proc;
        proc.kind = map_always_kind(item->always_kind);
        proc.body = item->body;
        mod->processes.push_back(proc);
        break;
    }
    case ModuleItemKind::ModuleInst: {
        RtlirModuleInst inst;
        inst.module_name = item->inst_module;
        inst.inst_name = item->inst_name;
        inst.resolved = nullptr;
        mod->children.push_back(inst);
        break;
    }
    case ModuleItemKind::ParamDecl:
        break;
    case ModuleItemKind::GenerateBlock:
        diag_.warning(item->loc, "generate blocks are not yet elaborated");
        break;
    }
}

void Elaborator::elaborate_items(ModuleDecl* decl, RtlirModule* mod) {
    for (auto* item : decl->items) {
        elaborate_item(item, mod);
    }
}

} // namespace delta
