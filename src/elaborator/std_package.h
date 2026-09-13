#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

// §G.1: the built-in standard package, std, has the contents Annex G
// describes -- the semaphore class, the mailbox class, the randomize
// function, the process class and the weak reference class -- each with a
// prototype of its own in §G.3 through §G.7. §G.2 adds that the package
// contains system types, the types of §26.7's std package, and that the
// semantics of each of its members are defined not in the annex but in the
// subclause its prototype indicates: §15.3 for semaphore, §15.4 for mailbox,
// §18.12 for randomize, §9.7 for process and §8.30 for weak_reference. This
// file is the one place the contents are written down: the compilation-unit
// scope registers the std package's class names from it, and any other
// reader of the std package asks it what the package holds and where each
// member's semantics live.

// §G.1: the five members, in the order the subclause lists them.
enum class StdPackageMember : std::uint8_t {
  kSemaphore,
  kMailbox,
  kRandomize,
  kProcess,
  kWeakReference,
};

// §G.1: four of the members are classes and one, randomize, is a function.
enum class StdPackageMemberKind : std::uint8_t { kClass, kFunction };

struct StdPackageEntry {
  StdPackageMember member = StdPackageMember::kSemaphore;
  std::string_view name;
  StdPackageMemberKind kind = StdPackageMemberKind::kClass;
  std::string_view defining_subclause;  // §G.2: where the semantics are
};

// §G.1: the contents of the std package, in the subclause's order.
const std::vector<StdPackageEntry>& StdPackageContents();

// §G.1: the name a member is declared under in the std package, its kind,
// and the member a name denotes, or none where the std package holds no
// member of that name.
std::string_view StdPackageMemberName(StdPackageMember member);
StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member);
std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name);

// §G.2: the subclause the semantics of a member are defined in, which the
// member's prototype in §G.3 through §G.7 indicates; and whether a subclause
// lies there, being that subclause or one beneath it, so that a diagnostic a
// std member's semantics raise can be seen to cite the place §G.2 points to.
std::string_view DefiningSubclauseOfStdPackageMember(StdPackageMember member);
bool StdPackageDefinesSemanticsIn(StdPackageMember member,
                                  std::string_view subclause);

// §G.2: the std package contains system types; a name denotes one iff it
// denotes a member of the package that is a class, randomize being a function
// and no type.
bool IsStdPackageSystemType(std::string_view name);

}  // namespace delta
