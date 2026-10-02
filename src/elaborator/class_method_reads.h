#ifndef DELTA_ELABORATOR_CLASS_METHOD_READS_H
#define DELTA_ELABORATOR_CLASS_METHOD_READS_H

#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct ModuleDecl;
struct ModuleItem;

// §23.9: every name a declaration of a compilation unit gives, in whichever
// scope it stands: the items of the unit, of its packages and of its modules,
// interfaces, programs and checkers with their ports and parameters; the
// members, parameters and type parameters of every class, nested ones among
// them; and every enumeration constant those declare. A name read in a class
// resolves, if at all, to one of these, so one none of them gives is
// unresolved wherever it is read. The set is wider than any one scope reaches,
// so it answers whether a name is declared at all, not whether it is visible.
class UnitDeclaredNames {
 public:
  explicit UnitDeclaredNames(const CompilationUnit* unit);

  // Whether some declaration of the unit gives `name`. A §6.19.2 member
  // written `name[N]` gives the constants its name with a number appended.
  bool Declares(std::string_view name) const;

 private:
  void AddItems(const std::vector<ModuleItem*>& items);
  void AddScope(const ModuleDecl* scope);
  void AddClass(const ClassDecl* cls);
  void AddEnumerations(const DataType& type);

  std::unordered_set<std::string_view> names_;
  std::unordered_set<std::string_view> numbered_enum_names_;
};

// §23.9: reports each name a method of a class of `unit` reads that neither
// the method declares, as a formal or in its body, nor any declaration of the
// unit gives (UnitDeclaredNames).
void ReportClassMethodUnresolved(const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CLASS_METHOD_READS_H
