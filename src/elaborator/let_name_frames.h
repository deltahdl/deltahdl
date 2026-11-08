#pragma once

#include <cstdint>
#include <deque>
#include <span>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace delta {

struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct ImportItem;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct Stmt;

enum class NameKind : std::uint8_t {
  kLet,
  kVariable,
  kTypedef,
  kClass,
  kOther
};

struct NameFrame;

struct NameBinding {
  NameKind kind = NameKind::kOther;
  const ModuleItem* item = nullptr;
  const ClassDecl* cls = nullptr;
  const DataType* type = nullptr;
  const std::vector<Expr*>* dims = nullptr;
  const NameFrame* scope = nullptr;
};

struct NameFrame {
  explicit NameFrame(const NameFrame* enclosing) : outer(enclosing) {}
  NameFrame(const NameFrame&) = delete;
  NameFrame& operator=(const NameFrame&) = delete;

  const NameFrame* outer;
  std::unordered_map<std::string_view, NameBinding> names;
  std::vector<const NameFrame*> bases;
};

const NameBinding* FindName(const NameFrame& frame, std::string_view name);

const NameBinding* FindOwnName(const NameFrame* frame, std::string_view name);

inline constexpr int kMaxTypedefHops = 32;

const DataType* TypedefTypeOf(const NameBinding* named);

class PackageFrames {
 public:
  explicit PackageFrames(const CompilationUnit* unit);
  const NameFrame* Find(std::string_view package) const;
  const std::vector<std::pair<const PackageDecl*, const NameFrame*>>& All()
      const {
    return packages_;
  }

 private:
  std::deque<NameFrame> frames_;
  std::vector<std::pair<const PackageDecl*, const NameFrame*>> packages_;
  NameFrame std_{nullptr};
};

class ClassFrames {
 public:
  ClassFrames(const PackageFrames& packages, const NameFrame& unit)
      : packages_(packages), unit_(unit) {}

  const NameFrame* Of(const ClassDecl& cls, const NameFrame& declaring);

  const NameFrame* MembersOf(const ClassDecl& cls, const NameFrame& declaring);

  const NameBinding* TypeName(const DataType& type, const NameFrame& scope);

  const NameFrame* PrefixClassMembers(const DataType& type,
                                      const NameFrame& scope);

 private:
  const NameBinding* Named(std::span<const std::string_view> prefixes,
                           std::string_view name, const NameFrame& scope);
  const NameFrame* ScopeNamed(std::span<const std::string_view> prefixes,
                              const NameFrame& scope);
  const NameFrame* OutermostScope(std::string_view prefix,
                                  const NameFrame& scope);
  const NameFrame* ClassFrame(const NameBinding* named);
  const NameBinding* ThroughTypedefs(const NameBinding* named);
  const NameFrame* BaseFrame(std::string_view name, std::string_view scope,
                             const NameFrame& declaring);

  const PackageFrames& packages_;
  const NameFrame& unit_;
  std::deque<NameFrame> frames_;
  std::unordered_map<const ClassDecl*, const NameFrame*> built_;
};

void DeclareOther(NameFrame& frame, std::string_view name);

void DeclareScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                  const PackageFrames& packages);

void DeclareUnitScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                      const CompilationUnit& unit,
                      const PackageFrames& packages);

void DeclareImplicitNets(NameFrame& frame,
                         const std::vector<ModuleItem*>& items);

void DeclareHeader(NameFrame& frame, const ModuleDecl& decl);

void DeclareStatements(NameFrame& frame, const std::vector<Stmt*>& stmts,
                       const PackageFrames& packages);

void DeclareStatementScope(NameFrame& frame, const Stmt* s,
                           const PackageFrames& packages);

}  // namespace delta
