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

  void Excuse() { read_ = true; }

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

struct RecordedRun {
  SourceManager mgr;
  Watched<bool> has_errors;
  Watched<std::vector<Diagnostic>> diags;

  RecordedRun() = default;
  RecordedRun(RecordedRun&&) noexcept = default;
  RecordedRun& operator=(RecordedRun&&) noexcept = default;
  RecordedRun(const RecordedRun&) = delete;
  RecordedRun& operator=(const RecordedRun&) = delete;

  ~RecordedRun() {
    if (!has_errors.Peek() || has_errors.WasRead() || diags.WasRead()) return;
    ReportUnreadErrors(diags.Peek(), "read has_errors or diags",
                       mgr.FileContent(1));
  }
};

struct ParseResult : RecordedRun {
  Arena arena;
  CompilationUnit* cu = nullptr;
};

inline void RecordDiagnostics(const DiagEngine& diag, RecordedRun& result) {
  result.has_errors = diag.HasErrors();
  result.diags = diag.Diagnostics();
}

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

inline bool ParseWithPreprocessorOk(const std::string& src) {
  return !ParseWithPreprocessor(src).has_errors;
}
