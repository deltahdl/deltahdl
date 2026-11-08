#pragma once

#include <functional>
#include <span>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;
struct PackageDecl;
struct Stmt;

struct ProceduralLocal {
  std::string_view name;
  const DataType* type;
  const std::vector<Expr*>* unpacked_dims;
};

using TypeRefResolver = std::function<std::vector<Expr*>(
    DataType&, SourceLoc, std::span<const ProceduralLocal>)>;

using ProceduralStmtVisitor =
    std::function<void(Stmt*, std::span<const ProceduralLocal>)>;

void ResolveProceduralTypeRefs(ModuleItem* item,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena,
                               const ProceduralStmtVisitor& visit = {});

void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          const CompilationUnit* unit, Arena& arena,
                          const ProceduralStmtVisitor& visit = {});

struct UnitScopeTypeRef {
  const Expr* operand;
  SourceLoc loc;
  const PackageDecl* package;
  std::vector<ProceduralLocal> locals;
};

void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena,
                              std::vector<UnitScopeTypeRef>& written);

void ResolveUnitScopeProcedureTypeRefs(
    CompilationUnit* unit, Arena& arena,
    const std::function<void(const PackageDecl*)>& enter,
    const TypeRefResolver& resolve, const ProceduralStmtVisitor& visit);

}  // namespace delta
