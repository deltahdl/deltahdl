#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

// §G.1: the built-in standard package, std, has the contents Annex G
// describes -- the semaphore class, the mailbox class, the randomize
// function, the process class and the weak reference class -- each with a
// prototype of its own in §G.3 through §G.7 and, as §G.2 says, semantics
// defined in the subclause that prototype names. This file is the one place
// the contents are written down: the compilation-unit scope registers the
// std package's class names from it, and any other reader of the std package
// asks it what the package holds.

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
};

// §G.1: the contents of the std package, in the subclause's order.
const std::vector<StdPackageEntry>& StdPackageContents();

// §G.1: the name a member is declared under in the std package, its kind,
// and the member a name denotes, or none where the std package holds no
// member of that name.
std::string_view StdPackageMemberName(StdPackageMember member);
StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member);
std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name);

}  // namespace delta
