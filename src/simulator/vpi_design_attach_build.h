#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/source_loc.h"
#include "elaborator/rtlir_attribute.h"

namespace delta {

class Arena;
class SimContext;
struct ClassDecl;
struct ClassMember;
struct CompilationUnit;
struct ConstraintDistItem;
struct DataType;
struct EventExpr;
enum class DataTypeKind : uint8_t;
enum class StmtKind : uint8_t;
enum class TokenKind : uint16_t;
struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct PropertyExprNode;
struct SeqLinearBody;
struct RtlirAssertion;
struct RtlirDesign;
struct RtlirImport;
struct RtlirModule;
struct RtlirNet;
struct RtlirPort;
struct RtlirVariable;
struct Stmt;
struct UdpDecl;
struct VpiDeferredCall;
struct VpiObject;

using VpiObjectMap = std::unordered_map<std::string_view, VpiObject*>;

struct VpiAttachBuild {
  std::function<VpiObject*()> alloc;
  std::function<std::string_view(std::string)> keep;
  Arena& arena;
  std::vector<VpiDeferredCall>* deferred_calls = nullptr;
  const VpiObjectMap& unit_typespecs = NoTypespecs();

  static const VpiObjectMap& NoTypespecs() {
    static const VpiObjectMap kNone;
    return kNone;
  }
};

using VpiNameKeeper = std::function<std::string_view(std::string)>;

VpiObject* VpiIntConstant(int64_t value, const VpiAttachBuild& build);

int VpiTypespecKind(DataTypeKind kind);

int VpiDataTypeVariableKind(DataTypeKind kind);

int VpiNetObjectKind(const RtlirNet& net);

void RecordNetObjectKinds(const RtlirDesign* design,
                          const VpiObjectMap& objects);

using PackedDims = std::vector<PackedRange>;

int64_t PackedDimsWidth(const PackedDims& dims);

std::optional<PackedDims> DeclaredPackedDims(const DataType* type,
                                             uint32_t width, SimContext& ctx);

PackedDims WrittenPackedDims(const DataType* type, SimContext& ctx);

std::optional<PackedRange> WrittenUnpackedDim(const Expr* dim, SimContext& ctx);

void VpiRecordWrittenDims(VpiObject& array, const std::vector<Expr*>& dims,
                          SimContext& ctx);

std::vector<RtlirNet> VpiDeclaredNets(const RtlirModule& mod);

bool VpiNetIsInterconnect(const RtlirNet& net);

std::vector<RtlirVariable> VpiDeclaredVariables(const RtlirModule& mod);

std::vector<std::string> VpiDeclaredNetKeys(const RtlirNet& net,
                                            const std::string& prefix);

void AttachVectorBits(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

void AttachArrayElements(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build);

void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build);

VpiObject* VpiImportedTypespec(std::string_view name,
                               const std::vector<RtlirImport>& imports,
                               const VpiObjectMap& answered);

VpiObject* VpiPackageOrUnitTypespec(std::string_view package,
                                    std::string_view name,
                                    const std::vector<RtlirImport>& imports,
                                    const VpiObjectMap& answered);

void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiObjectMap& unit_typespecs, SimContext& ctx,
                      const VpiAttachBuild& build);

std::string VpiScopedFullName(const VpiObject* scope, std::string_view name);

using VpiSubroutineObjects =
    std::map<std::pair<const ModuleItem*, std::string>, VpiObject*>;

const ModuleDecl& VpiElementDeclFrom(const ModuleDecl* holder,
                                     const CompilationUnit& unit,
                                     std::string_view name);

const ModuleDecl& VpiDeclOf(const RtlirModule& mod);

VpiSubroutineObjects AttachSubroutines(const RtlirDesign& design,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build);

struct VpiCalledSubroutine {
  const ModuleItem* decl = nullptr;
  VpiObject* object = nullptr;
};

struct VpiCallSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const VpiObject* scope;
  const VpiSubroutineObjects& made;
  const std::vector<std::string_view>* gen_prefixes = nullptr;
  std::function<bool(const Expr& call, VpiObject* made)> shape_call = nullptr;
  std::string_view package = {};
  const VpiObject* formals = nullptr;
};

VpiCalledSubroutine VpiPackageSubroutine(const RtlirDesign& design,
                                         std::string_view package,
                                         std::string_view name,
                                         const VpiSubroutineObjects& made);

VpiCalledSubroutine VpiNamedSubroutine(const VpiCallSite& site,
                                       std::string_view name);

VpiCalledSubroutine VpiCalleeSubroutine(const VpiCallSite& site,
                                        const Expr& callee);

bool VpiIsPackageScopedName(const Expr& name);

using VpiCalleeResolver = std::function<VpiObject*(const Expr& callee)>;

VpiCalleeResolver VpiCalleesAt(const VpiCallSite& site);

using VpiClassDefnObjects =
    std::map<std::pair<const ClassDecl*, std::string>, VpiObject*>;

struct VpiClassCallSite {
  const RtlirModule* mod = nullptr;
  std::string_view package;
};
using VpiClassCallSites =
    std::unordered_map<const VpiObject*, VpiClassCallSite>;

VpiClassDefnObjects AttachClassDefinitions(const RtlirDesign* design,
                                           const VpiObjectMap& objects,
                                           SimContext& ctx,
                                           const VpiAttachBuild& build,
                                           VpiClassCallSites& sites);

VpiObject* VpiNamedClassDefn(const VpiClassDefnObjects& defns,
                             std::string_view written,
                             const std::string& prefix);

VpiObjectMap AttachTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& classes,
                             SimContext& ctx, const VpiAttachBuild& build);

void AttachClassVarTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& defns, SimContext& ctx,
                             const VpiAttachBuild& build);

void AttachVariableAndNetRanges(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build);

void AttachDeclaredRanges(VpiObject* obj, const DataType& type,
                          const std::vector<Expr*>& unpacked_dims,
                          SimContext& ctx, const VpiAttachBuild& build);

VpiObject* VpiBitAtOffset(const VpiObject& root, int64_t offset);

int VpiBinaryOpType(TokenKind op);

int VpiUnaryOpType(TokenKind op);

int VpiIncDecOpType(TokenKind op, bool postfix);

bool VpiIsDynamicPrefixHolderType(int type);

const VpiObject* VpiScopeOrInstance(const VpiObject* scope,
                                    const VpiObjectMap& objects,
                                    const std::string& instance);

VpiObject* VpiClockingBlockAround(const VpiObject* scope,
                                  const VpiObjectMap& objects,
                                  const std::string& instance,
                                  std::string_view name);

VpiObject* VpiPrefixedReference(VpiObject* holder, std::string_view written,
                                const std::function<VpiObject*()>& alloc,
                                const VpiNameKeeper& keep);

VpiObject* VpiInstanceExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const std::string& prefix, SimContext& ctx,
                                 const VpiAttachBuild& build);

struct VpiCallStand {
  VpiObject* scope;
  const RtlirModule* mod = nullptr;
  std::string_view package = {};
};

struct VpiExprNames {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen_prefixes;
  const VpiObject* scope = nullptr;
  const RtlirNodeAttributes* attrs = nullptr;
  const VpiCallStand* stand = nullptr;
  const RtlirModule* mod = nullptr;
  const VpiObject* instance = nullptr;
};

VpiObject* VpiGenBlockExpression(const Expr* expr, const VpiExprNames& names,
                                 SimContext& ctx, const VpiAttachBuild& build);

struct VpiDeferredCall {
  const Expr* call;
  VpiObject* made;
  VpiCallStand stand;
  std::string prefix;
  std::vector<std::string_view> gen_prefixes;
};

VpiObject* VpiCallSiteExpression(const Expr* expr, const VpiObjectMap& objects,
                                 const VpiCallSite& site, SimContext& ctx,
                                 const VpiAttachBuild& build);

struct VpiAssignedSide {
  const Expr* expr;
  const VpiObject* target;
};

VpiObject* VpiCallSiteAssignedExpression(const VpiAssignedSide& side,
                                         const VpiObjectMap& objects,
                                         const VpiCallSite& site,
                                         SimContext& ctx,
                                         const VpiAttachBuild& build);

int VpiBuiltInClassCallKind(std::string_view cls, std::string_view method);

bool VpiIsClassBuiltInMethod(std::string_view method);

int VpiMemberBuiltInCallKind(std::string_view method);

enum class VpiBuiltInHolder : uint8_t {
  kNone,
  kString,
  kEnum,
  kFixedArray,
  kDynamicArray,
  kAssocArray,
  kQueue,
  kCovergroup,
  kEvent,
};

struct VpiStmtBuild {
  const VpiAttachBuild& build;
  std::function<VpiObject*(const Expr*)> expression;
  std::function<VpiObject*(const Stmt*, VpiObject*)> statement;
  std::function<int(const Expr*)> index_kind;
  std::function<VpiObject*(const Expr*, const VpiObject*)> assigned;
  std::function<VpiObject*(int, std::string_view, std::string_view)>
      assertion_decl;
};

int VpiBuiltStmtKind(const Stmt& stmt);

int VpiBareAtomicKind(StmtKind kind);

VpiObject* VpiEventCondition(const std::vector<EventExpr>& events,
                             const VpiStmtBuild& with);

void VpiFillAssertionClock(VpiObject* obj, const Stmt& property,
                           const VpiStmtBuild& with);

VpiObject* VpiMakePropertySpec(VpiObject* holder, const Stmt& property,
                               const VpiStmtBuild& with);

struct VpiPropertySpecParts {
  const std::vector<EventExpr>& clock;
  const Expr* disable = nullptr;
  const PropertyExprNode* property = nullptr;
};

VpiObject* VpiSequenceExprObject(const SeqLinearBody& body,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing);

VpiObject* VpiPropertyExprObject(const PropertyExprNode* node,
                                 const VpiStmtBuild& with,
                                 const std::vector<EventExpr>* flowing);

VpiObject* VpiMakePropertySpecOf(VpiObject* holder,
                                 const VpiPropertySpecParts& parts,
                                 const VpiStmtBuild& with);

VpiObject* VpiRangeObject(VpiObject* parent,
                          const std::optional<PackedRange>& bounds,
                          const VpiAttachBuild& build);

void VpiFillStmt(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with);

struct VpiRegisteredSystf {
  VpiObject* object = nullptr;
  int type = 0;
  int sysfunctype = 0;
};

using VpiCallSiteObjects =
    std::map<std::pair<const Expr*, std::string>, VpiObject*>;

using VpiStmtObjects =
    std::map<std::pair<const Stmt*, std::string>, VpiObject*>;

void VpiResolveDisableTargets(const VpiStmtObjects& stmts);

struct VpiCallBuild {
  SimContext& ctx;
  std::function<VpiRegisteredSystf(std::string_view)> systf;
  VpiCallSiteObjects& sites;
  VpiStmtObjects& stmts;
  const VpiClassDefnObjects& classes;
  const VpiSubroutineObjects& subroutines;
  const VpiObjectMap& unit_typespecs;
};

struct VpiCallObjects {
  VpiClassDefnObjects classes;
  VpiSubroutineObjects subroutines;
  VpiObjectMap unit_typespecs;
  VpiClassCallSites class_sites;
  const RtlirDesign* design = nullptr;
};

void VpiShapeDeferredCalls(const RtlirDesign* design,
                           const VpiObjectMap& objects,
                           std::vector<VpiDeferredCall>& deferred,
                           const VpiCallBuild& calls,
                           const VpiAttachBuild& build);

PackedRange VpiEvaluatedRange(Expr* left, Expr* right, SimContext& ctx);

VpiObject* VpiMakeInstanceArray(VpiObject* holder, int kind,
                                std::string_view name, const PackedRange& range,
                                const VpiAttachBuild& build);

void VpiAddArrayElement(VpiObject* array, VpiObject* element, int64_t index,
                        const VpiAttachBuild& build);

void AttachClockingBlocks(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

void AttachAliasStatements(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build);

void AttachDefaultDisableIffs(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

VpiObject* VpiMakeItemAssertion(const RtlirAssertion& assertion,
                                VpiObject* scope, SimContext& ctx,
                                const VpiStmtBuild& with);

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx);

void VpiRecordWrittenLocation(VpiObject* obj, SourceLoc loc, SimContext& ctx);

void AttachInstanceArrays(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

using VpiUdpDefnOf = std::function<VpiObject*(const UdpDecl*)>;

void AttachPrimitives(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiUdpDefnOf& udp_defn_of, SimContext& ctx,
                      const VpiAttachBuild& build);

void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build);

void VpiAttachAttributes(VpiObject* owner,
                         const std::vector<ResolvedAttribute>& attrs,
                         bool on_definition, SimContext& ctx,
                         const VpiAttachBuild& build);

const std::vector<ResolvedAttribute>& VpiNodeAttributes(const RtlirModule* mod,
                                                        const void* node);

const std::vector<ResolvedAttribute>& VpiNodeAttributes(
    const RtlirNodeAttributes* table, const void* node);

void AttachPortAttributes(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build);

void AttachAttributes(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build);

void AttachGenBlockStorage(const RtlirDesign* design,
                           const VpiObjectMap& objects);

void AttachGenBlockInstances(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiNameKeeper& keep);

void VpiMakePortBits(VpiObject* port, const VpiAttachBuild& build);

void AttachPortConnections(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build);

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build);

struct VpiItemSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const std::vector<std::string_view>& gen_prefixes;
  VpiObject* scope;
};

std::function<bool(const Expr& call, VpiObject* made)> VpiItemCallShaper(
    const VpiItemSite& site, const VpiObjectMap& objects,
    const VpiCallBuild& calls, const VpiAttachBuild& build);

VpiObject* VpiBaseClassDefn(const VpiObject* defn);

VpiObject* VpiClassNameScope(const VpiObject* defn, VpiObject* outer,
                             const VpiAttachBuild& build);

struct VpiConstraintNames {
  const VpiObjectMap& objects;
  const std::string& prefix;
  const std::vector<std::string_view>& gen;
  VpiObject* scope;
  SimContext& ctx;
  const RtlirNodeAttributes* attrs = nullptr;
  const VpiCallStand* stand = nullptr;
};

VpiObject* VpiMakeConstraint(const ClassMember& block, VpiObject* holder,
                             const VpiConstraintNames& names,
                             const VpiAttachBuild& build);

VpiObject* VpiMakeDistribution(
    VpiObject* weighted, const std::vector<ConstraintDistItem>& items,
    const std::function<VpiObject*()>& alloc,
    const std::function<VpiObject*(const Expr*)>& expression);

void AttachModports(const RtlirDesign* design, const VpiObjectMap& objects,
                    SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
