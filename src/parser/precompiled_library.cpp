#include "parser/precompiled_library.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <ios>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/protect_license.h"

namespace delta {

namespace {

// DPLIB005 records carry the directive state, the runtime licences, the
// protected lines and the envelopes' viewports beside the text; a DPLIB004
// file, which held no viewports, a DPLIB003 file, which held no protected lines
// either, a DPLIB002 file, which held no licences either, and a DPLIB001 file,
// which held the text alone, are not read.
constexpr char kMagic[] = "DPLIB005";
constexpr std::streamsize kMagicLen = 8;

void WriteU32(std::ofstream& os, uint32_t v) {
  unsigned char buf[4] = {
      static_cast<unsigned char>(v),
      static_cast<unsigned char>(v >> 8),
      static_cast<unsigned char>(v >> 16),
      static_cast<unsigned char>(v >> 24),
  };
  os.write(reinterpret_cast<const char*>(buf), 4);
}

bool ReadU32(std::ifstream& is, uint32_t& v) {
  unsigned char buf[4];
  if (!is.read(reinterpret_cast<char*>(buf), 4)) return false;
  v = static_cast<uint32_t>(buf[0]) | (static_cast<uint32_t>(buf[1]) << 8) |
      (static_cast<uint32_t>(buf[2]) << 16) |
      (static_cast<uint32_t>(buf[3]) << 24);
  return true;
}

bool ReadBytes(std::ifstream& is, std::string& out, uint32_t n) {
  out.resize(n);
  if (n == 0) return true;
  return static_cast<bool>(is.read(out.data(), n));
}

void WriteU8(std::ofstream& os, uint8_t v) {
  os.write(reinterpret_cast<const char*>(&v), 1);
}

bool ReadU8(std::ifstream& is, uint8_t& v) {
  return static_cast<bool>(is.read(reinterpret_cast<char*>(&v), 1));
}

void WriteU64(std::ofstream& os, uint64_t v) {
  WriteU32(os, static_cast<uint32_t>(v));
  WriteU32(os, static_cast<uint32_t>(v >> 32));
}

bool ReadU64(std::ifstream& is, uint64_t& v) {
  uint32_t lo = 0;
  uint32_t hi = 0;
  if (!ReadU32(is, lo) || !ReadU32(is, hi)) return false;
  v = static_cast<uint64_t>(lo) | (static_cast<uint64_t>(hi) << 32);
  return true;
}

void WriteString(std::ofstream& os, std::string_view s) {
  WriteU32(os, static_cast<uint32_t>(s.size()));
  if (!s.empty()) os.write(s.data(), static_cast<std::streamsize>(s.size()));
}

bool ReadString(std::ifstream& is, std::string& s) {
  uint32_t len = 0;
  return ReadU32(is, len) && ReadBytes(is, s, len);
}

// One design element's directive state, field by field in declaration order.
// The enumerations are written as their underlying values, which is what
// ReadModuleDirectives casts them back from.
void WriteModuleDirectives(std::ofstream& os, const ModuleDirectives& d) {
  WriteString(os, d.module);
  WriteU64(os, d.decay_ticks);
  WriteU8(os, d.decay_infinite ? 1 : 0);
  WriteU32(os, d.strength);
  WriteU8(os, d.has_strength ? 1 : 0);
  WriteU8(os, static_cast<uint8_t>(d.delay_mode));
  WriteU8(os, d.has_timescale ? 1 : 0);
  WriteU8(os, static_cast<uint8_t>(d.timescale.unit));
  WriteU32(os, static_cast<uint32_t>(d.timescale.magnitude));
  WriteU8(os, static_cast<uint8_t>(d.timescale.precision));
  WriteU32(os, static_cast<uint32_t>(d.timescale.prec_magnitude));
  WriteU8(os, d.is_package ? 1 : 0);
  WriteU8(os, static_cast<uint8_t>(d.default_nettype));
  WriteU8(os, static_cast<uint8_t>(d.unconnected_drive));
}

// The values ReadModuleDirectives reads one field of a record into before it is
// converted to the field's own type.
struct DirectiveBytes {
  uint8_t decay_infinite = 0;
  uint8_t has_strength = 0;
  uint8_t delay_mode = 0;
  uint8_t has_timescale = 0;
  uint8_t unit = 0;
  uint32_t magnitude = 0;
  uint8_t precision = 0;
  uint32_t prec_magnitude = 0;
  uint8_t is_package = 0;
  uint8_t default_nettype = 0;
  uint8_t unconnected_drive = 0;
};

bool ReadModuleDirectives(std::ifstream& is, ModuleDirectives& d) {
  DirectiveBytes b;
  bool read = ReadString(is, d.module) && ReadU64(is, d.decay_ticks) &&
              ReadU8(is, b.decay_infinite) && ReadU32(is, d.strength) &&
              ReadU8(is, b.has_strength) && ReadU8(is, b.delay_mode) &&
              ReadU8(is, b.has_timescale) && ReadU8(is, b.unit) &&
              ReadU32(is, b.magnitude) && ReadU8(is, b.precision) &&
              ReadU32(is, b.prec_magnitude) && ReadU8(is, b.is_package) &&
              ReadU8(is, b.default_nettype) && ReadU8(is, b.unconnected_drive);
  if (!read) return false;
  d.decay_infinite = b.decay_infinite != 0;
  d.has_strength = b.has_strength != 0;
  d.delay_mode = static_cast<DelayModeDirective>(b.delay_mode);
  d.has_timescale = b.has_timescale != 0;
  d.timescale.unit = static_cast<TimeUnit>(static_cast<int8_t>(b.unit));
  d.timescale.magnitude = static_cast<int>(b.magnitude);
  d.timescale.precision =
      static_cast<TimeUnit>(static_cast<int8_t>(b.precision));
  d.timescale.prec_magnitude = static_cast<int>(b.prec_magnitude);
  d.is_package = b.is_package != 0;
  d.default_nettype = static_cast<NetType>(b.default_nettype);
  d.unconnected_drive = static_cast<NetType>(b.unconnected_drive);
  return true;
}

// One runtime licence, part by part. Only licences the reading found stated
// are recorded (Preprocessor::ApplyLicense), so `stated` is not written and is
// restored by ReadRuntimeLicense.
void WriteRuntimeLicense(std::ofstream& os, const ProtectLicense& license) {
  WriteString(os, license.library);
  WriteString(os, license.entry);
  WriteString(os, license.feature);
  WriteString(os, license.exit);
  WriteU8(os, license.has_exit ? 1 : 0);
  WriteU64(os, license.match);
  WriteU8(os, license.has_match ? 1 : 0);
}

bool ReadRuntimeLicense(std::ifstream& is, ProtectLicense& license) {
  uint8_t has_exit = 0;
  uint8_t has_match = 0;
  bool read = ReadString(is, license.library) &&
              ReadString(is, license.entry) &&
              ReadString(is, license.feature) && ReadString(is, license.exit) &&
              ReadU8(is, has_exit) && ReadU64(is, license.match) &&
              ReadU8(is, has_match);
  if (!read) return false;
  license.has_exit = has_exit != 0;
  license.has_match = has_match != 0;
  license.stated = true;
  return true;
}

void WriteViewport(std::ofstream& os, const PrecompiledViewport& viewport) {
  WriteString(os, viewport.object);
  WriteString(os, viewport.access);
  WriteU32(os, viewport.line);
  WriteU32(os, viewport.first_line);
  WriteU32(os, viewport.last_line);
}

bool ReadViewport(std::ifstream& is, PrecompiledViewport& viewport) {
  return ReadString(is, viewport.object) && ReadString(is, viewport.access) &&
         ReadU32(is, viewport.line) && ReadU32(is, viewport.first_line) &&
         ReadU32(is, viewport.last_line);
}

void WriteDirectives(std::ofstream& os, const PrecompiledDirectives& d) {
  WriteU32(os, static_cast<uint32_t>(d.modules.size()));
  for (const ModuleDirectives& m : d.modules) WriteModuleDirectives(os, m);
  WriteU32(os, static_cast<uint32_t>(d.cell_modules.size()));
  for (const std::string& name : d.cell_modules) WriteString(os, name);
  WriteU32(os, static_cast<uint32_t>(d.runtime_licenses.size()));
  for (const ProtectLicense& license : d.runtime_licenses) {
    WriteRuntimeLicense(os, license);
  }
  WriteU32(os, static_cast<uint32_t>(d.protected_lines.size()));
  for (uint32_t line : d.protected_lines) WriteU32(os, line);
  WriteU32(os, static_cast<uint32_t>(d.viewports.size()));
  for (const PrecompiledViewport& viewport : d.viewports) {
    WriteViewport(os, viewport);
  }
}

// Reads a count and that many entries into `out`, each with `read_one`. Each
// entry is read before it is kept, so a damaged count ends the read at the
// stream's end rather than asking for room for entries that are not there.
template <typename T, typename ReadOne>
bool ReadList(std::ifstream& is, std::vector<T>& out, ReadOne read_one) {
  uint32_t count = 0;
  if (!ReadU32(is, count)) return false;
  for (uint32_t i = 0; i < count; ++i) {
    T entry{};
    if (!read_one(is, entry)) return false;
    out.push_back(std::move(entry));
  }
  return true;
}

bool ReadDirectives(std::ifstream& is, PrecompiledDirectives& d) {
  return ReadList(is, d.modules, ReadModuleDirectives) &&
         ReadList(is, d.cell_modules, ReadString) &&
         ReadList(is, d.runtime_licenses, ReadRuntimeLicense) &&
         ReadList(is, d.protected_lines, ReadU32) &&
         ReadList(is, d.viewports, ReadViewport);
}

// Parses `source`, the preprocessor's output, with every report suppressed, and
// answers the unit it parsed to, or null where it does not parse. The report
// of a parse error is the business of the caller that has the source's path.
const CompilationUnit* ParseSilently(std::string_view source,
                                     SourceManager& mgr, Arena& arena) {
  DiagEngine diag(mgr);
  diag.PushSuppress();
  uint32_t fid = mgr.AddFile("<precompile>", std::string(source));
  Lexer lex(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  Parser parser(lex, arena, diag);
  const CompilationUnit* cu = parser.Parse();
  if (diag.SuppressedErrorCount() != 0) return nullptr;
  return cu;
}

bool ParsesCleanly(std::string_view source) {
  SourceManager mgr;
  Arena arena;
  return ParseSilently(source, mgr, arena) != nullptr;
}

// Appends one (library, source) record to the file at `path`, opening the file
// with the format marker when the record is its first. Returns true only once
// every byte has reached the filesystem: a caller told the write succeeded can
// take the record to be there, which is what a form the next invocation of the
// tool will read has to mean.
bool AppendRecord(std::string_view source, std::string_view library,
                  const std::filesystem::path& path, bool first,
                  const PrecompiledDirectives& directives) {
  std::ofstream os(path, std::ios::binary | std::ios::app);
  if (!os.good()) return false;
  if (first) os.write(kMagic, kMagicLen);

  WriteString(os, library);
  WriteString(os, source);
  WriteDirectives(os, directives);
  os.flush();
  return os.good();
}

// Puts the file back to the length it had before an append that did not
// finish. The cells already written are the ones earlier compiles put there,
// and a half-written record following them would cost every one of them its
// readability, so the remnant goes rather than the library. A file the failed
// append itself created had no length to go back to and is removed.
void DiscardPartialRecord(const std::filesystem::path& path,
                          std::uintmax_t previous_size) {
  std::error_code ec;
  if (previous_size == 0) {
    std::filesystem::remove(path, ec);
    return;
  }
  std::filesystem::resize_file(path, previous_size, ec);
}

// Records which library the record's declarations were compiled into, on every
// kind of declaration AppendCellDeclarations moves. The two lists have to
// agree: a cell reaches a bind through FindNamedInLibrary, which matches on the
// library name as well as the cell name, so a declaration moved onto the target
// without a library tag is a declaration no bind can name.
void TagCells(CompilationUnit& cu, std::string_view library, Arena& arena) {
  auto* buf = static_cast<char*>(arena.Allocate(library.size(), 1));
  std::copy_n(library.data(), library.size(), buf);
  std::string_view view{buf, library.size()};
  for (auto* m : cu.modules) m->library = view;
  for (auto* i : cu.interfaces) i->library = view;
  for (auto* p : cu.programs) p->library = view;
  for (auto* c : cu.checkers) c->library = view;
  for (auto* u : cu.udps) u->library = view;
  for (auto* p : cu.packages) p->library = view;
  for (auto* c : cu.configs) c->library = view;
}

// One record as the file holds it: the library its cells were compiled into,
// the preprocessed text and the directive state recorded beside it.
struct Record {
  std::string library;
  std::string source;
  PrecompiledDirectives directives;
};

// Reads a single record from the stream. Returns false on any read failure.
bool ReadRecord(std::ifstream& is, Record& record) {
  return ReadString(is, record.library) && ReadString(is, record.source) &&
         ReadDirectives(is, record.directives);
}

// Bundles the destination compilation unit together with the shared parsing
// infrastructure (source manager, arena, diagnostics) that a load pass writes
// into. These travel together through PrecompiledLibrary::Load and LoadRecord.
struct LoadContext {
  CompilationUnit& target;
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
};

template <typename Decl>
void DropCells(std::vector<Decl*>& cells, std::string_view library,
               const std::unordered_set<std::string_view>& names) {
  std::erase_if(cells, [&](const Decl* cell) {
    return cell->library == library && names.contains(cell->name);
  });
}

// §33.3.1 (printed page 937): "If multiple cells with the same name map to the
// same library, then the last cell encountered shall be written to the
// library. This is to support a "separate-compile" use model ... where it is
// assumed that encountering a cell after it has previously been compiled is
// intended to be a recompiling of the cell." Each record is a later encounter
// than every record before it, so a cell it declares replaces whatever cell of
// that name the library already holds -- in the one namespace modules,
// interfaces, programs, checkers, primitives and configurations share, and
// among packages in theirs. Kept side by side, the two were one definition too
// many for the bind.
void ReplaceRecompiledCells(CompilationUnit& target, const CompilationUnit& cu,
                            std::string_view library) {
  std::unordered_set<std::string_view> definitions;
  for (const auto* list :
       {&cu.modules, &cu.interfaces, &cu.programs, &cu.checkers}) {
    for (const auto* m : *list) definitions.insert(m->name);
  }
  for (const auto* u : cu.udps) definitions.insert(u->name);
  for (const auto* c : cu.configs) definitions.insert(c->name);
  DropCells(target.modules, library, definitions);
  DropCells(target.interfaces, library, definitions);
  DropCells(target.programs, library, definitions);
  DropCells(target.checkers, library, definitions);
  DropCells(target.udps, library, definitions);
  DropCells(target.configs, library, definitions);
  std::unordered_set<std::string_view> packages;
  for (const auto* p : cu.packages) packages.insert(p->name);
  DropCells(target.packages, library, packages);
}

// Registers one record's text under `path`. Where lines of it came out of a
// decryption envelope, the text is registered beside a copy marked protected
// and those lines take their origin from the copy, so a position on one
// resolves to protected code (§37.3.6) at the same path and line as before.
uint32_t RegisterRecordText(const std::filesystem::path& path, Record& record,
                            SourceManager& mgr) {
  const std::vector<uint32_t>& sealed = record.directives.protected_lines;
  if (sealed.empty())
    return mgr.AddFile(path.string(), std::move(record.source));
  const uint32_t kCopy = mgr.AddFile(path.string(), record.source);
  mgr.MarkProtected(kCopy);
  std::vector<OutputLineOrigin> origins(
      static_cast<std::size_t>(std::ranges::count(record.source, '\n')) + 1);
  for (uint32_t line : sealed) {
    if (line == 0 || line > origins.size()) continue;
    origins[line - 1] = OutputLineOrigin{kCopy, line};
  }
  return mgr.AddPreprocessedFile(path.string(), std::move(record.source),
                                 std::move(origins));
}

// §34.5.32: the viewports of the envelopes a record's text came out of, each
// envelope restated as the lines of `fid`, the record's registered text, and
// each viewport standing where its pragma expression stood in it.
void AddRecordViewports(const Record& record, uint32_t fid,
                        SourceManager& mgr) {
  for (const PrecompiledViewport& kept : record.directives.viewports) {
    EnvelopeViewport viewport;
    viewport.object = kept.object;
    viewport.access = kept.access;
    viewport.loc = SourceLoc{fid, kept.line, 1};
    viewport.region_source = fid;
    viewport.first_line = kept.first_line;
    viewport.last_line = kept.last_line;
    mgr.AddViewport(std::move(viewport));
  }
}

// Parses one record's source into the target compilation unit, applying the
// directive state it recorded and tagging cells with the record's library name.
// Returns false on parse failure.
bool LoadRecord(const std::filesystem::path& path, Record& record,
                LoadContext& ctx) {
  uint32_t fid = RegisterRecordText(path, record, ctx.mgr);
  AddRecordViewports(record, fid, ctx.mgr);
  Lexer lex(ctx.mgr.FileContent(fid), fid, ctx.diag,
            TextOrigin::kPreprocessorOutput);
  Parser parser(lex, ctx.arena, ctx.diag);
  auto* cu = parser.Parse();
  if (cu == nullptr || ctx.diag.HasErrors()) return false;

  MarkCellModules(cu, record.directives.cell_modules);
  ApplyModuleDirectives(cu, record.directives.modules);
  const std::string& library = record.library;
  TagCells(*cu, library, ctx.arena);
  ReplaceRecompiledCells(ctx.target, *cu, library);
  AppendCellDeclarations(ctx.target, *cu);
  return true;
}

// Opens the file at `path` for reading its records, past the format marker;
// false where it is not a file this tool wrote.
bool OpenRecords(const std::filesystem::path& path, std::ifstream& is) {
  is.open(path, std::ios::binary);
  if (!is.good()) return false;
  char magic[kMagicLen];
  if (!is.read(magic, kMagicLen)) return false;
  return std::memcmp(magic, kMagic, kMagicLen) == 0;
}

}  // namespace

bool PrecompiledLibrary::Save(std::string_view source, std::string_view library,
                              const std::filesystem::path& path,
                              const PrecompiledDirectives& directives) {
  // A compile puts cells into a library. One asked to compile under no library
  // name has none to put them in, and the cells it wrote would answer to no
  // library when something later came looking for them there.
  if (library.empty()) return false;
  if (!ParsesCleanly(source)) return false;

  std::error_code ec;
  std::uintmax_t held = 0;
  if (std::filesystem::exists(path, ec)) {
    held = std::filesystem::file_size(path, ec);
    if (ec) return false;
  }

  if (!AppendRecord(source, library, path, held == 0, directives)) {
    DiscardPartialRecord(path, held);
    return false;
  }
  return true;
}

std::vector<std::string> PrecompiledLibrary::CellNames(
    std::string_view source) {
  SourceManager mgr;
  Arena arena;
  const CompilationUnit* cu = ParseSilently(source, mgr, arena);
  std::vector<std::string> names;
  if (cu == nullptr) return names;
  for (const auto* list :
       {&cu->modules, &cu->interfaces, &cu->programs, &cu->checkers}) {
    for (const auto* m : *list) names.emplace_back(m->name);
  }
  for (const auto* u : cu->udps) names.emplace_back(u->name);
  for (const auto* c : cu->configs) names.emplace_back(c->name);
  return names;
}

bool PrecompiledLibrary::Load(const std::filesystem::path& path,
                              CompilationUnit& target, SourceManager& mgr,
                              Arena& arena, DiagEngine& diag) {
  std::ifstream is;
  if (!OpenRecords(path, is)) return false;

  LoadContext ctx{target, mgr, arena, diag};
  while (true) {
    if (is.peek() == EOF) break;
    Record record;
    if (!ReadRecord(is, record)) return false;
    if (!LoadRecord(path, record, ctx)) return false;
  }
  return true;
}

std::vector<ProtectLicense> PrecompiledLibrary::RuntimeLicenses(
    const std::filesystem::path& path) {
  std::vector<ProtectLicense> licenses;
  std::ifstream is;
  if (!OpenRecords(path, is)) return licenses;
  while (is.peek() != EOF) {
    Record record;
    if (!ReadRecord(is, record)) return {};
    for (ProtectLicense& license : record.directives.runtime_licenses) {
      licenses.push_back(std::move(license));
    }
  }
  return licenses;
}

}  // namespace delta
