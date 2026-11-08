#pragma once

#include <string_view>

namespace delta {

class Arena;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;

struct CalleeDeclaration {
  const DataType* result = nullptr;
  const ClassTypeInfo* cls = nullptr;
  std::string_view package;
};

CalleeDeclaration DeclarationOfCallee(const Expr* callee, SimContext& ctx,
                                      Arena& arena);

const ClassTypeInfo* ClassBehindHandle(const Expr* base, SimContext& ctx,
                                       Arena& arena);

}  // namespace delta
