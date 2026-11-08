#pragma once

#include <initializer_list>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

struct ClassDecl;
struct DataType;
struct Expr;
struct StructMember;

struct BlockParent {
  VpiObject* scope;
  const std::string& path;
  const Stmt* block = nullptr;
  const BlockParent* outer = nullptr;
  const VpiObject* formals = nullptr;
};

struct BodyWalk {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const VpiObjectMap& objects;
  const std::string& prefix;
  const VpiCallBuild& calls;
  const VpiAttachBuild& build;
  VpiObject* process = nullptr;
  const GenBlockPrefixes* gen_prefixes = nullptr;
  std::string_view package = {};
};

struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
  std::vector<std::string_view> prefix_members = {};
  bool user_defined = false;
  VpiObject* systf = nullptr;
  VpiObject* called = nullptr;
  int sysfunctype = 0;
};

inline const std::vector<Stmt*>& BlockItems(const Stmt& block) {
  return block.kind == StmtKind::kFork ? block.fork_stmts : block.stmts;
}

VpiCallSite CallSiteOf(const BlockParent& parent, const BodyWalk& walk);

int TypeVariableKind(const DataType& type, const BodyWalk& walk);

const Stmt* BlockVarDecl(const BlockParent& parent, std::string_view name,
                         const BlockParent*& where);

bool ChainNames(const Expr& expr, std::vector<std::string_view>& names);

int ForeachIndexKind(const Expr* array, const BlockParent& parent,
                     const BodyWalk& walk);

VpiObject* MethodCallClassDefn(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk);

bool ShapeExprCall(const Expr& call, VpiObject* made, const BlockParent& parent,
                   const BodyWalk& walk);

struct VpiScopedClass {
  const ClassDecl* decl = nullptr;
  std::string scope;
};

std::string_view VpiClassNameOf(const BodyWalk& walk, std::string_view name);

VpiScopedClass VpiFindClassDecl(const BodyWalk& walk, std::string_view name,
                                std::string_view package = {});

const ModuleItem* VpiMethodNamed(const ClassDecl& cls, std::string_view name);

struct VpiHeldClass {
  std::string_view name;
  std::span<const DataType> args;
};

VpiHeldClass VpiBaseOf(const ClassDecl& decl, std::span<const DataType> args);

struct VpiDeclaredMember {
  const ClassMember* member = nullptr;
  const ClassDecl* decl = nullptr;
  std::span<const DataType> args;
};

VpiDeclaredMember VpiMemberNamed(const BodyWalk& walk, ClassMemberKind kind,
                                 VpiHeldClass held, std::string_view name,
                                 std::string_view package = {});

struct VpiPropertyType {
  const DataType* type = nullptr;
  std::string_view scope;
};

VpiPropertyType VpiPropertyTypeOf(const VpiDeclaredMember& found);

const Stmt* VpiNamedBlockVarDecl(const RtlirModule& mod, std::string_view block,
                                 std::string_view name);

const ModuleItem* VpiInterfaceItem(const RtlirDesign& design,
                                   std::string_view iface,
                                   std::string_view name,
                                   std::initializer_list<ModuleItemKind> kinds);

const DataType* VpiStructTypeOf(const BodyWalk& walk, const DataType* type);

const DataType* VpiMemberStructType(const BodyWalk& walk,
                                    const StructMember& member);

const DataType* VpiMemberStructNamed(const BodyWalk& walk,
                                     const DataType& aggregate,
                                     std::string_view name);

CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk);

}  // namespace delta
