#include "simulator/foreign_code.h"

#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace delta {

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm() {
  return ForeignCodeRedistributionForm::kSharedObject;
}

bool ForeignCodeGuidelinesAreCommonToApplications() { return true; }

bool ForeignCodeAnnexApplies(ForeignCodeInterface included_through) {
  return included_through == ForeignCodeInterface::kDpi;
}

bool ForeignCodeIsLimitedToCOrCpp() { return false; }

ForeignCodeForm ForeignCodeProvidedForm() {
  return ForeignCodeForm::kObjectCode;
}

bool ForeignCodeObjectFormMustBeSupported() { return true; }

std::array<ForeignCodeFacility, 3> ForeignCodeFacilitiesDefined() {
  return {ForeignCodeFacility::kSpecifyLocationOfFiles,
          ForeignCodeFacility::kSpecifyFilesToLoad,
          ForeignCodeFacility::kProvideObjectCode};
}

bool ForeignCodeObjectMayBePackagedAs(
    ForeignCodeObjectPackaging /*packaging*/) {
  return true;
}

uint32_t ForeignCodeImplementationsUsuallyRequired() { return 2; }

ForeignCodeInclusionMethod ForeignCodeMethodOftenCovering(
    ForeignCodeUseCase use_case) {
  return use_case == ForeignCodeUseCase::kVendorIp
             ? ForeignCodeInclusionMethod::kBootstrapFile
             : ForeignCodeInclusionMethod::kToolSwitches;
}

bool ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase /*use_case*/) {
  return true;
}

bool ForeignCodeSwitchNamesAreRequirements() { return false; }

std::string_view ForeignCodeBootstrapHeader() { return "#!SV_LIBRARIES"; }

namespace {

bool IsBlank(char c) { return c == ' ' || c == '\t' || c == '\r'; }

// The entry a line holds, or an error where the line is not one entry
// preceded by a blank; a line of blanks alone is neither an entry nor a
// comment, and so an error too.
std::string ParseBootstrapEntry(std::string_view line, std::size_t line_no,
                                std::string* error) {
  if (line.empty() || !IsBlank(line.front())) {
    *error = "line " + std::to_string(line_no) +
             ": a library entry shall be preceded by at least one blank";
    return "";
  }
  std::size_t begin = 0;
  while (begin < line.size() && IsBlank(line[begin])) ++begin;
  if (begin == line.size()) {
    *error = "line " + std::to_string(line_no) +
             ": a line holds one library entry or a comment, and this holds "
             "neither";
    return "";
  }
  std::size_t end = begin;
  while (end < line.size() && !IsBlank(line[end])) ++end;
  std::size_t rest = end;
  while (rest < line.size() && IsBlank(line[rest])) ++rest;
  if (rest != line.size()) {
    *error = "line " + std::to_string(line_no) +
             ": a line holds exactly one library entry, and this holds more";
    return "";
  }
  return std::string(line.substr(begin, end - begin));
}

// The line starting at `pos`, without its newline; `pos` moves past it.
std::string_view NextLine(std::string_view text, std::size_t* pos) {
  const std::size_t kNewline = text.find('\n', *pos);
  const std::size_t kEnd =
      kNewline == std::string_view::npos ? text.size() : kNewline;
  std::string_view line = text.substr(*pos, kEnd - *pos);
  *pos = kNewline == std::string_view::npos ? text.size() : kNewline + 1;
  return line;
}

// §J.4.1 c): a comment line starts with # after any number of blanks.
bool IsCommentLine(std::string_view line) {
  std::size_t first = 0;
  while (first < line.size() && IsBlank(line[first])) ++first;
  return first < line.size() && line[first] == '#';
}

std::string MissingHeaderError() {
  return "line 1: the first line of a bootstrap file contains " +
         std::string(ForeignCodeBootstrapHeader());
}

}  // namespace

ForeignCodeBootstrap ParseForeignCodeBootstrap(std::string_view text) {
  ForeignCodeBootstrap file;
  std::size_t line_no = 0;
  std::size_t pos = 0;
  while (pos < text.size()) {
    const std::string_view kLine = NextLine(text, &pos);
    ++line_no;
    if (line_no == 1) {
      // §J.4.1 a): the first line contains the header string.
      if (kLine.find(ForeignCodeBootstrapHeader()) == std::string_view::npos) {
        file.error = MissingHeaderError();
        return file;
      }
      continue;
    }
    if (IsCommentLine(kLine)) continue;
    // §J.4.1 b): otherwise the line holds one entry.
    std::string entry = ParseBootstrapEntry(kLine, line_no, &file.error);
    if (!file.Ok()) return file;
    file.libraries.push_back(entry);
  }
  if (line_no == 0) file.error = MissingHeaderError();
  return file;
}

std::string_view ForeignCodeRootSwitch() { return "-sv_root"; }

void ForeignCodeLocator::SetRoot(std::string_view directory) {
  root_ = std::string(directory);
}

bool ForeignCodeLocator::HasRoot() const { return !root_.empty(); }

std::string ForeignCodeLocator::Root() const {
  if (HasRoot()) return root_;
  std::error_code ec;
  const std::filesystem::path kCwd = std::filesystem::current_path(ec);
  return ec ? std::string(".") : kCwd.string();
}

std::string ForeignCodeLocator::Resolve(std::string_view path) const {
  const std::filesystem::path kPath(path);
  if (kPath.is_absolute()) return kPath.string();
  return (std::filesystem::path(Root()) / kPath).string();
}

std::string_view ForeignCodeLibListSwitch() { return "-sv_liblist"; }

std::string_view ForeignCodeLibSwitch() { return "-sv_lib"; }

std::string_view ForeignCodeSwitchOf(ForeignCodeSpecificationMethod method) {
  return method == ForeignCodeSpecificationMethod::kBootstrapFileEntry
             ? ForeignCodeLibListSwitch()
             : ForeignCodeLibSwitch();
}

bool ForeignCodeSwitchMayRepeat(std::string_view switch_name) {
  return switch_name == ForeignCodeLibListSwitch() ||
         switch_name == ForeignCodeLibSwitch();
}

bool ForeignCodeMethodsAreAvailableConcurrently() { return true; }

bool ForeignCodeMethodsMayBeMixed() { return true; }

std::string_view ForeignCodeSharedLibraryExtension() {
#if defined(_WIN32)
  return ".dll";
#elif defined(__APPLE__)
  return ".dylib";
#else
  return ".so";
#endif
}

std::string ForeignCodeSharedLibraryFileName(
    std::string_view pathname_without_extension) {
  return std::string(pathname_without_extension) +
         std::string(ForeignCodeSharedLibraryExtension());
}

ForeignCodeParty ForeignCodeResponsibleFor(ForeignCodeDuty duty) {
  const bool kExtension = duty == ForeignCodeDuty::kIdentifyTheExtension ||
                          duty == ForeignCodeDuty::kAppendTheExtension;
  return kExtension ? ForeignCodeParty::kApplication
                    : ForeignCodeParty::kProvider;
}

ForeignCodeLoadScope ForeignCodeLoadRequired() {
  return ForeignCodeLoadScope::kReferencedObjectCodeOnly;
}

bool ForeignCodeIsSameFile(std::string_view a, std::string_view b) {
  const std::filesystem::path kA(a);
  const std::filesystem::path kB(b);
  if (kA.lexically_normal() == kB.lexically_normal()) return true;
  std::error_code ec;
  const bool kSame =
      std::filesystem::equivalent(ForeignCodeSharedLibraryFileName(a),
                                  ForeignCodeSharedLibraryFileName(b), ec);
  return !ec && kSame;
}

namespace {

// Appends `path` under `method` unless a library already in the order is the
// same file, an earlier occurrence taking precedence over a later one.
void LoadOnce(std::string_view path, ForeignCodeSpecificationMethod method,
              std::vector<ForeignCodeLibrary>* order) {
  for (const ForeignCodeLibrary& loaded : *order) {
    if (ForeignCodeIsSameFile(loaded.path, path)) return;
  }
  order->push_back({std::string(path), method});
}

}  // namespace

std::vector<ForeignCodeLibrary> ForeignCodeLoadOrder(
    const std::vector<std::string>& bootstrap_entries,
    const std::vector<std::string>& lib_switch_values) {
  std::vector<ForeignCodeLibrary> order;
  for (const std::string& entry : bootstrap_entries) {
    LoadOnce(entry, ForeignCodeSpecificationMethod::kBootstrapFileEntry,
             &order);
  }
  for (const std::string& value : lib_switch_values) {
    LoadOnce(value, ForeignCodeSpecificationMethod::kLibSwitch, &order);
  }
  return order;
}

std::vector<std::string> ForeignCodeResolveBootstrapEntries(
    const ForeignCodeBootstrap& file, std::string_view root) {
  ForeignCodeLocator locator;
  locator.SetRoot(root);
  std::vector<std::string> resolved;
  resolved.reserve(file.libraries.size());
  for (const std::string& entry : file.libraries) {
    resolved.push_back(locator.Resolve(entry));
  }
  return resolved;
}

std::vector<std::string> ForeignCodeLibraryFileNames(
    const std::vector<ForeignCodeLibrary>& order) {
  std::vector<std::string> names;
  names.reserve(order.size());
  for (const ForeignCodeLibrary& library : order) {
    names.push_back(ForeignCodeSharedLibraryFileName(library.path));
  }
  return names;
}

}  // namespace delta
