#include "elaborator/assertion_name_rules.h"

#include <algorithm>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

bool IsAssertionTextItem(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
      return true;
    default:
      return false;
  }
}

bool Holds(const std::vector<std::string_view>& names, std::string_view name) {
  return std::find(names.begin(), names.end(), name) != names.end();
}

// The names a declaration's own body may read beside the enclosing scope's:
// its formals and its local variables.
bool DeclaresLocally(const ModuleItem* item, std::string_view name) {
  if (Holds(item->prop_formals, name) ||
      Holds(item->prop_seq_assert_vars, name) ||
      Holds(item->assertion_local_names, name)) {
    return true;
  }
  for (const SeqLocalDecl& local : item->prop_locals) {
    if (local.name == name) return true;
  }
  return false;
}

// Whether the text of `item` names `callee`, by an instance written with or
// without an argument list.
bool Instantiates(const ModuleItem* item, std::string_view callee) {
  if (Holds(item->prop_instance_refs, callee)) return true;
  for (const AssertionRead& read : item->assertion_reads) {
    if (read.name == callee) return true;
  }
  for (const AssertionInstanceArg& arg : item->assertion_instance_args) {
    if (arg.callee == callee) return true;
  }
  return false;
}

using DeclsByName = std::unordered_map<std::string_view, const ModuleItem*>;

DeclsByName SequenceAndPropertyDecls(const ModuleDecl* decl) {
  DeclsByName decls;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        item->kind == ModuleItemKind::kPropertyDecl) {
      decls.emplace(item->name, item);
    }
  }
  return decls;
}

// §16.10: the sequence or property `item` instantiates that declares `name`
// as a local variable, or nullptr.
const ModuleItem* OwnerOfInvisibleLocal(const ModuleItem* item,
                                        std::string_view name,
                                        const DeclsByName& decls) {
  for (const auto& [callee, owner] : decls) {
    if (owner == item || !DeclaresLocally(owner, name) ||
        Holds(owner->prop_formals, name) || !Instantiates(item, callee)) {
      continue;
    }
    return owner;
  }
  return nullptr;
}

void ReportRead(const ModuleItem* item, const AssertionRead& read,
                const DeclsByName& decls, DiagEngine& diag) {
  if (const ModuleItem* owner = OwnerOfInvisibleLocal(item, read.name, decls)) {
    diag.Error(
        read.loc,
        std::format("'{}' is a local variable of {} '{}' and is not "
                    "visible outside its body",
                    read.name,
                    owner->kind == ModuleItemKind::kSequenceDecl ? "sequence"
                                                                 : "property",
                    owner->name),
        Subclause("16.10"));
    return;
  }
  diag.Error(read.loc,
             std::format("reference to unresolved identifier '{}'", read.name),
             Subclause("23.9"));
}

// The sequence or property `arg` is passed to by `item`, when the formal it
// binds is written in a cycle delay or a repetition bound and the actual is a
// variable rather than one of `item`'s own formals; null otherwise.
const ModuleItem* CalleeTakingAVariableAsAConstant(
    const ModuleItem* item, const AssertionInstanceArg& arg,
    const DeclsByName& decls,
    const std::function<bool(std::string_view)>& is_variable) {
  auto it = decls.find(arg.callee);
  if (it == decls.end()) return nullptr;
  const ModuleItem* callee = it->second;
  if (arg.index >= callee->prop_formals.size()) return nullptr;
  if (!Holds(callee->assertion_const_names, callee->prop_formals[arg.index]) ||
      Holds(item->prop_formals, arg.name) || !is_variable(arg.name)) {
    return nullptr;
  }
  return callee;
}

}  // namespace

void ReportAssertionUnresolved(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& declared, DiagEngine& diag) {
  DeclsByName decls = SequenceAndPropertyDecls(decl);
  std::unordered_set<std::string_view> scope_names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) {
      scope_names.insert(item->name);
    }
  }
  for (const ModuleItem* item : decl->items) {
    if (!IsAssertionTextItem(item->kind)) continue;
    for (const AssertionRead& read : item->assertion_reads) {
      if (DeclaresLocally(item, read.name) || decls.count(read.name) != 0 ||
          scope_names.count(read.name) != 0 || declared(read.name)) {
        continue;
      }
      ReportRead(item, read, decls, diag);
    }
  }
}

void ReportNonConstantBoundActuals(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& is_variable,
    DiagEngine& diag) {
  DeclsByName decls = SequenceAndPropertyDecls(decl);
  for (const ModuleItem* item : decl->items) {
    if (!IsAssertionTextItem(item->kind)) continue;
    for (const AssertionInstanceArg& arg : item->assertion_instance_args) {
      const ModuleItem* callee =
          CalleeTakingAVariableAsAConstant(item, arg, decls, is_variable);
      if (callee == nullptr) continue;
      std::string_view formal = callee->prop_formals[arg.index];
      diag.Error(arg.loc,
                 std::format(
                     "the actual argument '{}' bound to the formal '{}' of "
                     "{} '{}' is not an elaboration-time constant, and the "
                     "formal is written in a cycle delay or a repetition "
                     "bound",
                     arg.name, formal,
                     callee->kind == ModuleItemKind::kSequenceDecl ? "sequence"
                                                                   : "property",
                     callee->name),
                 Subclause("16.8"));
    }
  }
}

}  // namespace delta
