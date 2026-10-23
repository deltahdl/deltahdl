#pragma once

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// A member of RecordedRun that notes whether the case it was handed to ever
// read it. Every way a case reads one arrives at Get: has_errors is read
// through its conversion to bool, in EXPECT_TRUE, EXPECT_FALSE, an `if` or a
// `!`, and diags through its conversion to the vector ReportedError takes, its
// size and emptiness, or the iteration FindDiag and a range-for do. Assigning
// to it is no read, so a case handed a freshly recorded run still owes one.
//
// A move carries the read to the new object and counts the old one as read, so
// a result returned or assigned by value is reported once.
template <typename T>
class Watched {
 public:
  Watched() = default;
  Watched(Watched&& other) noexcept
      : value_(std::move(other.value_)), read_(other.read_) {
    other.read_ = true;
  }
  Watched& operator=(Watched&& other) noexcept {
    value_ = std::move(other.value_);
    read_ = other.read_;
    other.read_ = true;
    return *this;
  }
  Watched(const Watched&) = delete;
  Watched& operator=(const Watched&) = delete;
  ~Watched() = default;

  Watched& operator=(T value) {
    value_ = std::move(value);
    read_ = false;
    return *this;
  }

  operator const T&() const { return Get(); }
  auto size() const { return Get().size(); }
  bool empty() const { return Get().empty(); }
  auto begin() const { return Get().begin(); }
  auto end() const { return Get().end(); }

  // For a case that a defect of deltahdl's fails, which names the issue filed
  // for it beside the call and drops the call with the fix.
  void Excuse() { read_ = true; }

  // What RecordedRun looks at as it is destroyed, neither of them a read.
  bool WasRead() const { return read_; }
  const T& Peek() const { return value_; }

 private:
  const T& Get() const {
    read_ = true;
    return value_;
  }

  T value_{};
  mutable bool read_ = false;
};

// What a fixture run hands a case once the engine that recorded the run is
// gone: the source manager holding the case's source, and the diagnostics. The
// diagnostics are a copy rather than a view: the engine is a local of the call
// that ran the tool, so a case reading the engine's own record would be reading
// storage released before the call returned.
//
// has_errors stays beside them, because a case asking only whether a source
// was accepted is asking a question the whole record does not answer more
// clearly than the boolean does.
//
// A tool that rejects a source still leaves behind what it built or the state
// it ended in, so a case asserting an absence or a default there holds whether
// the rule it covers works or not. A case that read has_errors or diags has
// taken the rejection into account, whatever it concluded from them. One that
// read neither passed on a source that was never accepted, and the destructor
// reports that, the end of the record's life being the last moment anybody
// could still have looked. Since the engine is gone by then, the record and
// whether it was read are kept here rather than on the engine, as Diagnosed in
// fixture_diagnosed.h keeps them for the fixtures that own their engine.
struct RecordedRun {
  SourceManager mgr;
  Watched<bool> has_errors;
  Watched<std::vector<Diagnostic>> diags;

  RecordedRun() = default;
  RecordedRun(RecordedRun&&) noexcept = default;
  RecordedRun& operator=(RecordedRun&&) noexcept = default;
  RecordedRun(const RecordedRun&) = delete;
  RecordedRun& operator=(const RecordedRun&) = delete;

  // The report quotes the first file the run registered, which every entry
  // point registers the case's own source as.
  ~RecordedRun() {
    if (!has_errors.Peek() || has_errors.WasRead() || diags.WasRead()) return;
    ReportUnreadErrors(diags.Peek(), "read has_errors or diags",
                       mgr.FileContent(1));
  }
};

// What a run of the parser left behind for a case to make its claim about: the
// record of the run and the CompilationUnit the parser built, which for a
// rejected source holds whatever the parser recovered.
struct ParseResult : RecordedRun {
  Arena arena;
  CompilationUnit* cu = nullptr;
};

// Takes both readings of the engine at once, so no run can copy the record and
// leave the boolean behind, or the reverse. Neither assignment is a read of
// the result, so the case it is handed to still owes one.
inline void RecordDiagnostics(const DiagEngine& diag, RecordedRun& result) {
  result.has_errors = diag.HasErrors();
  result.diags = diag.Diagnostics();
}

// The diagnostic a run recorded whose message contains `needle`, or nullptr
// when the run recorded none. A case asserting which rule of IEEE 1800-2023 a
// rejection enforced reads the subclause off the report it is about rather than
// off whichever report the run happened to write first: one source can be
// rejected for more than one reason, and diags.front() is then a different
// rule's report.
inline const Diagnostic* FindDiag(const ParseResult& result,
                                  std::string_view needle) {
  for (const auto& diag : result.diags) {
    if (diag.message.find(needle) != std::string::npos) return &diag;
  }
  return nullptr;
}

inline ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  RecordDiagnostics(diag, result);
  return result;
}

// Answers whether the parser accepted `src`, for a case that asks nothing else
// about the run. Parse is what runs, so the answer here and the record a case
// reading Parse gets come from one parse of one source rather than from two
// that could drift apart.
inline bool ParseOk(const std::string& src) { return !Parse(src).has_errors; }

inline ParseResult ParseLibrary(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.ParseLibraryText();
  RecordDiagnostics(diag, result);
  return result;
}

inline ParseResult ParseWithPreprocessor(const std::string& src) {
  ParseResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  // Registered with its origins, as the AddPreprocessedFile call in
  // ParseSource in src/main.cpp registers it, so a report this fixture
  // provokes is formatted the way the binary formats it.
  auto pp_fid = result.mgr.AddPreprocessedFile("<preprocessed>", pp,
                                               preproc.LineOrigins());
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.cu->default_nettype = preproc.DefaultNetType();
  result.cu->unconnected_drive = preproc.UnconnectedDrive();
  for (auto* mod : result.cu->modules) {
    for (const auto& cell_name : preproc.CellModuleNames()) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
  result.cu->default_decay_time = preproc.DefaultDecayTime();
  result.cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.cu->default_trireg_strength = preproc.DefaultTriregStrength();
  result.cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.cu->delay_mode_directive = preproc.DelayModeDirective();
  RecordDiagnostics(diag, result);
  return result;
}

// The preprocessed counterpart of ParseOk, and written on the call above for
// the same reason.
inline bool ParseWithPreprocessorOk(const std::string& src) {
  return !ParseWithPreprocessor(src).has_errors;
}
