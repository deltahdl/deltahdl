#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct ClassDecl;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;
struct Variable;

uint32_t SimParamTypeWidth(const DataType& type, const ScopeMap& scope,
                           const SimContext& ctx);

bool SimParamTypeIsSigned(const DataType& type, const SimContext& ctx);

class ClassParamSizer {
 public:
  explicit ClassParamSizer(const ClassDecl* decl) : decl_(decl) {}

  ClassParamSizer(const ClassDecl* decl, std::string_view type_scope)
      : decl_(decl), type_scope_(type_scope) {}

  const ClassDecl* Decl() const { return decl_; }

  Logic4Vec Value(size_t i, const Expr* expr, SimContext& ctx, Arena& arena);

  Logic4Vec Value(std::string_view name, const DataType* type, const Expr* expr,
                  SimContext& ctx, Arena& arena);

  void Record(size_t i, const Logic4Vec& val);

  void UseTypeActuals(const std::vector<DataType>* actuals) {
    type_actuals_ = actuals;
  }

 private:
  const DataType* TypeParamType(std::string_view name) const;

  const ClassDecl* decl_;
  std::string_view type_scope_;
  ScopeMap scope_;
  const std::vector<DataType>* type_actuals_ = nullptr;
};

struct ClassParamBinding {
  std::string_view name;
  Variable* value = nullptr;
  const DataType* type = nullptr;
};
void MarkUnboundedClassParams(ClassObject* obj, const ClassDecl* decl);

void ShapeClassParamLocal(const ClassDecl* decl, size_t i, Variable* local,
                          SimContext& ctx, Arena& arena);

std::vector<ClassParamBinding> CollectClassParamBindings(
    const ClassTypeInfo* cls, SimContext& ctx);
void RebindClassParamBindings(const std::vector<ClassParamBinding>& bindings,
                              SimContext& ctx);

using ParamValueLookup = std::function<const Logic4Vec*(std::string_view)>;
using ParamValueStore = std::function<void(std::string_view, const Logic4Vec&)>;

struct ClassParamStorage {
  ParamValueLookup header;
  ParamValueStore store;
  ClassTypeInfo* sized = nullptr;
};

void FoldClassBodyParams(ClassParamSizer sizer,
                         const ClassParamStorage& storage, SimContext& ctx,
                         Arena& arena);

ClassParamStorage ClassStaticStorage(ClassTypeInfo* info);

TypedefMap TypeParamTypes(const ClassDecl* decl,
                          const std::vector<DataType>& actuals,
                          const SimContext& ctx);

DataType ClassPropertyType(const DataType& type, const ClassDecl* cls,
                           const TypedefMap& type_params);

}  // namespace delta
