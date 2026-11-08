#pragma once

#include <string>
#include <string_view>

namespace delta {

struct AssocArrayObject;
struct ClassMember;
struct ClassDecl;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct ModuleItem;
struct Stmt;
class SimContext;
class Arena;

const ModuleItem* ClassScopeTypedefItem(const ClassTypeInfo* from,
                                        std::string_view name);

const ModuleItem* TypedefItemSeenFrom(const DataType& type,
                                      const ClassTypeInfo* from,
                                      SimContext& ctx);

const ModuleItem* PropertyNamedTypedef(const ClassMember* member,
                                       const ClassTypeInfo* declaring,
                                       SimContext& ctx);

const ModuleItem* PropertyTypedefItem(const ClassMember* member,
                                      const ClassTypeInfo* declaring,
                                      SimContext& ctx);

const Stmt* DeclShapedByTypedef(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

AssocArrayObject* ClassAssocProperty(ClassObject* obj,
                                     const ClassTypeInfo* from,
                                     std::string_view name, SimContext& ctx);

bool IsAssocPropertyDecl(const ClassMember* member,
                         const ClassTypeInfo* declaring, SimContext& ctx);

AssocArrayObject* FindAssocArrayOfName(std::string_view name, SimContext& ctx,
                                       ClassObject** owner = nullptr);

AssocArrayObject* FindAssocArrayOfBase(const Expr* base, SimContext& ctx,
                                       Arena& arena,
                                       ClassObject** owner = nullptr);

void TypeForeachIterVar(std::string_view iter_name, const AssocArrayObject* aa,
                        SimContext& ctx);

const DataType* TypeParamActual(const ClassObject* obj, const ClassDecl* decl,
                                std::string_view pname);

std::string_view TypeParamNamedBy(const ClassDecl* decl, std::string_view name);

std::string_view PropertyClassName(const ClassObject* obj,
                                   const ClassTypeInfo* from,
                                   std::string_view field, SimContext& ctx);

bool PropertyIsArray(const ClassTypeInfo* from, std::string_view field,
                     SimContext& ctx);

bool IsHandlePath(const Expr* expr);

ClassObject* HandleSideObject(const Expr* side, SimContext& ctx, Arena& arena);

std::string InstanceMemberKey(const Expr* access);

}  // namespace delta
