#pragma once

#include <string_view>

#include "elaborator/const_eval.h"

namespace delta {

struct ClassDecl;
struct ClassTypeInfo;
struct DataType;
struct StructTypeInfo;
class SimContext;

bool ClassHasValueParams(const ClassDecl& decl);

const DataType* ClassAggregateTypedef(const ClassDecl& decl,
                                      std::string_view name);

std::string_view RegisterSpecializationTypedefLayout(
    std::string_view spelled, const ClassTypeInfo& declarer,
    std::string_view name, const ScopeMap& scope, SimContext& ctx);

const ClassTypeInfo* ClassTypedefDeclarer(std::string_view name,
                                          const ClassTypeInfo& info,
                                          const ClassDecl& cls,
                                          const ClassDecl*& decl);

std::string_view ClassTypedefLayoutKey(const ClassTypeInfo& cls,
                                       std::string_view name, SimContext& ctx);

const StructTypeInfo* MethodClassTypedefLayout(std::string_view name,
                                               SimContext& ctx,
                                               std::string_view* key);

}  // namespace delta
