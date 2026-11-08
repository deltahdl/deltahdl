#pragma once

namespace delta {

struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

struct ModuleInUnit {
  const ModuleDecl& decl;
  const CompilationUnit& unit;
};

const ModuleItem* AttachedCallTarget(const Expr& call,
                                     const ModuleInUnit& scope);

}  // namespace delta
