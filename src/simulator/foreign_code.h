// Annex J: the inclusion of foreign language code into a SystemVerilog
// application. §J.1 has the annex describe common guidelines for that
// inclusion, whose intention is to enable the redistribution of C binaries in
// shared object form. This header states what the annex says; the switches
// and files the guidelines define are what a simulator's driver reads.
#ifndef DELTA_SIMULATOR_FOREIGN_CODE_H_
#define DELTA_SIMULATOR_FOREIGN_CODE_H_

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §J.1: what the guidelines of the annex are for -- the redistribution of C
// binaries -- and the form they intend it in.
enum class ForeignCodeRedistributionForm : uint8_t {
  kSharedObject,
  kSourceCode,
  kStaticArchiveOnly,
};

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm();

// §J.1: the guidelines are common ones, for the inclusion of foreign language
// code into any SystemVerilog application rather than into one simulator's.
bool ForeignCodeGuidelinesAreCommonToApplications();

// §J.2: foreign language code is functionality included into SystemVerilog
// using the DPI, so the annex applies only to code included through that
// interface, and code included through another, the VPI say, is outside the
// standard's scope. Most such code is created from C or C++ source, but
// nothing precludes object code from other languages, and the annex is
// independent of the language used. The code is provided in general as
// object code compiled for the platform, and every simulator shall support
// including it in that form as the annex specifies.
enum class ForeignCodeInterface : uint8_t { kDpi, kVpi };

bool ForeignCodeAnnexApplies(ForeignCodeInterface included_through);
bool ForeignCodeIsLimitedToCOrCpp();

enum class ForeignCodeForm : uint8_t { kObjectCode, kSourceCode };

ForeignCodeForm ForeignCodeProvidedForm();
bool ForeignCodeObjectFormMustBeSupported();

// §J.2: what the annex defines how to do -- specify the location of the
// files within the filesystem, specify the files to be loaded, and provide
// the object code, as a shared library or an archive.
enum class ForeignCodeFacility : uint8_t {
  kSpecifyLocationOfFiles,
  kSpecifyFilesToLoad,
  kProvideObjectCode,
};

std::array<ForeignCodeFacility, 3> ForeignCodeFacilitiesDefined();

enum class ForeignCodeObjectPackaging : uint8_t { kSharedLibrary, kArchive };

bool ForeignCodeObjectMayBePackagedAs(ForeignCodeObjectPackaging packaging);

// §J.2: the annex requires multiple implementations, usually two, of the
// facilities, users having different viewpoints: a vendor providing IP as
// foreign code wants a self-contained integration a third party can still
// make, often covered by a bootstrap file; a project team specifying a
// common set of foreign code that changes with technology, cells and
// back-annotation data is often covered by a set of tool switches; and a
// user switching between selections or adding code is covered by tool
// switches -- each of the three able to use the bootstrap file approach
// too. The switch names the annex defines are recommendations, not
// requirements of the language, naming being outside the standard and some
// character configurations impossible in some shells.
enum class ForeignCodeInclusionMethod : uint8_t {
  kBootstrapFile,
  kToolSwitches
};

enum class ForeignCodeUseCase : uint8_t { kVendorIp, kProjectTeam, kUser };

uint32_t ForeignCodeImplementationsUsuallyRequired();
ForeignCodeInclusionMethod ForeignCodeMethodOftenCovering(
    ForeignCodeUseCase use_case);
bool ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase use_case);
bool ForeignCodeSwitchNamesAreRequirements();

// §J.3: every path name the annex specifies is intended to be location
// independent, which the switch -sv_root accomplishes: it receives a single
// directory path name as its value, which is then prepended to any relative
// path name specified. In the absence of the switch, or for relative file
// names processed before any -sv_root specification, the user's current
// working directory is the default. A locator resolves each path name as it
// is processed, against the root in force at that moment.
std::string_view ForeignCodeRootSwitch();

class ForeignCodeLocator {
 public:
  // The directory a -sv_root specification gave, replacing any earlier one.
  void SetRoot(std::string_view directory);
  bool HasRoot() const;
  // The root relative path names are prepended with: the directory set, or
  // the user's current working directory while none is.
  std::string Root() const;
  // `path` as an absolute path name: itself where it is absolute already,
  // and the root followed by it where it is relative.
  std::string Resolve(std::string_view path) const;

 private:
  std::string root_;
};

// §J.4.1: the syntax of the object code bootstrap file. Its first line
// contains the string #!SV_LIBRARIES; an arbitrary number of entries follow,
// one per line, each holding exactly one library location -- the path name
// without extension of the object code file to be loaded, equivalent to the
// value of -sv_lib -- surrounded by any number of blanks, at least one blank
// preceding the entry in its line; and any number of comment lines, each
// starting with # after any number of blanks and ending at a newline, can
// be interspersed between the entries.
std::string_view ForeignCodeBootstrapHeader();

// The library locations a bootstrap file's text lists, in order, or a
// description of the first line that departs from the syntax -- a first line
// without the header, an entry no blank precedes, a line holding more than
// one entry, or a line that is neither an entry nor a comment.
struct ForeignCodeBootstrap {
  std::vector<std::string> libraries;
  std::string error;
  bool ok() const { return error.empty(); }
};

ForeignCodeBootstrap ParseForeignCodeBootstrap(std::string_view text);

}  // namespace delta

#endif  // DELTA_SIMULATOR_FOREIGN_CODE_H_
