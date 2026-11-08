#include "parser/parser_fsm.h"

#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_fsm.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

bool StandsBefore(SourceLoc a, SourceLoc b) {
  return a.file_id == b.file_id &&
         (a.line < b.line || (a.line == b.line && a.column < b.column));
}

ModuleDecl* ModuleHolding(const CompilationUnit& unit, SourceLoc loc) {
  for (ModuleDecl* mod : unit.modules) {
    if (!StandsBefore(loc, mod->range.start) &&
        StandsBefore(loc, mod->range.end)) {
      return mod;
    }
  }
  return nullptr;
}

std::string_view SignalEnumOf(const ModuleDecl& mod, std::string_view signal) {
  for (const ModuleItem* item : mod.items) {
    const bool kSignal = item->kind == ModuleItemKind::kVarDecl ||
                         item->kind == ModuleItemKind::kNetDecl;
    if (kSignal && item->name == signal && !item->fsm_enum.empty()) {
      return item->fsm_enum;
    }
  }
  return {};
}

std::vector<std::string_view> StatesOf(const ModuleDecl& mod,
                                       std::string_view enum_name) {
  std::vector<std::string_view> states;
  for (const ModuleItem* item : mod.items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->fsm_enum == enum_name) {
      states.push_back(item->name);
    }
  }
  return states;
}

void AddFsm(const CompilationUnit& unit, SourceLoc loc, FsmDecl fsm) {
  ModuleDecl* mod = ModuleHolding(unit, loc);
  if (mod == nullptr) return;
  if (fsm.enum_name.empty() && fsm.state_signals.size() == 1) {
    fsm.enum_name = SignalEnumOf(*mod, fsm.state_signals.front());
  }
  if (fsm.enum_name.empty()) return;
  fsm.states = StatesOf(*mod, fsm.enum_name);
  mod->fsms.push_back(std::move(fsm));
}

}  // namespace

void BindFsmPragmas(const Lexer& lexer, CompilationUnit& unit) {
  for (const Lexer::FsmStatePragma& pragma : lexer.FsmStatePragmas()) {
    if (pragma.form != Lexer::FsmStatePragma::Form::kStateVector) continue;
    FsmDecl fsm;
    fsm.state_signals.push_back(pragma.signal_name);
    if (pragma.has_enum) fsm.enum_name = pragma.enum_name;
    AddFsm(unit, pragma.loc, std::move(fsm));
  }
  for (const Lexer::FsmPartSelectPragma& pragma :
       lexer.FsmPartSelectPragmas()) {
    FsmDecl fsm;
    fsm.state_signals.push_back(pragma.signal_name);
    fsm.has_part_select = true;
    fsm.msb = pragma.msb;
    fsm.lsb = pragma.lsb;
    fsm.fsm_name = pragma.fsm_name;
    fsm.enum_name = pragma.enum_name;
    AddFsm(unit, pragma.loc, std::move(fsm));
  }
  for (const Lexer::FsmConcatPragma& pragma : lexer.FsmConcatPragmas()) {
    FsmDecl fsm;
    fsm.state_signals = pragma.signal_names;
    fsm.fsm_name = pragma.fsm_name;
    fsm.enum_name = pragma.enum_name;
    AddFsm(unit, pragma.loc, std::move(fsm));
  }
}

}  // namespace delta
