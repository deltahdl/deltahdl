#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parser/ast.h"
#include "simulator/vcd_writer.h"

namespace delta {

// §21.7 defines two dump files and no more: "a) 4-state: to represent variable
// changes in 0, 1, x, and z with no strength information. b) Extended: to
// represent variable changes in all states and strength information." The
// 4-state file is written by $dumpfile, $dumpvars and the control tasks
// §21.7.1.3 through §21.7.1.6 give them; the extended file by $dumpports and
// the control tasks §21.7.3.2 through §21.7.3.5 give it. §21.7.3.1 lets one
// source ask for both -- "The $dumpports task can be used in source code that
// also contains the $dumpvars task" -- so a run holds one dump of each, each
// with its own writer, file name and default name, and a task reaches the dump
// its own clause names.
//
// Everything a run holds of both files lives here rather than on SimContext.
// The two files are one feature with one clause behind them, and SimContext is
// the class every part of the simulator reaches through, so its header grew
// until an ordinary addition failed the file-size gate (#3463). What stays on
// SimContext is the handful of operations that need the rest of the run --
// opening a dump walks the variable table and arms a per-timestep callback,
// closing one stamps the current simulation time.
struct VcdDumpState {
  // §21.7.1.1 defaults the 4-state file to dump.vcd and §21.7.3.1 defaults the
  // extended file to dumpports.vcd, so each dump starts under its own name.
  VcdDump four_state{"dump.vcd"};
  VcdDump extended{"dumpports.vcd"};

  // The dump a VcdFileType names, so the open path can take the one the task
  // that called it writes.
  VcdDump& Dump(VcdFileType type);

  // A writer installed here stands in for both dumps. Whatever installed it --
  // the --vcd option, a test driver -- built one writer over one file and
  // settled its form, so there is no second file for the other form to go to.
  // Nothing here owns it.
  void SetVcdWriter(VcdWriter* vcd);
  // §21.7.1: the 4-state dump, or null when nothing has opened one.
  VcdWriter* GetVcdWriter() { return four_state.writer; }
  // §21.7.3.1: the extended dump, or null when no $dumpports has opened one.
  // Separate from GetVcdWriter because the two files are separate: a control
  // task reaching the wrong one writes its checkpoint into a file of the other
  // type, or into no file at all.
  VcdWriter* GetDumpportsWriter() { return extended.writer; }

  // §21.7.1.1: the name $dumpfile gives the 4-state file, which "is optional
  // and defaults to the string literal \"dump.vcd\" if not specified".
  void SetDumpFileName(std::string name);
  const std::string& GetDumpFileName() const;

  // §21.7.3.1: the name $dumpports gives the extended file -- "If no filename
  // is provided, the file shall be written to the current working directory
  // with the name dumpports.vcd". Held apart from the 4-state name because the
  // two files are two files: the defaults differ, and a source calling both
  // tasks names both.
  void SetDumpportsFileName(std::string name);
  const std::string& GetDumpportsFileName() const;

  // §21.7.2.3: the filename argument of $dumpfile exactly as written in the
  // source -- a string literal keeps its quotes, and a variable or expression
  // keeps its unevaluated source spelling. The $version section of the VCD
  // header reproduces this literal inside its $dumpfile(...) entry. Empty when
  // no $dumpfile call supplied a filename.
  void SetDumpFileLiteral(std::string text);
  const std::string& GetDumpFileLiteral() const;

  // §21.7.3.1 cross-call $dumpports bookkeeping: scope names and explicitly
  // specified file names must each be unique across all $dumpports calls.
  std::unordered_set<std::string> dumpports_scopes;
  std::unordered_set<std::string> dumpports_files;
  // §21.7.4.1: the $dumpports commands that executed before the extended dump
  // was opened, in call order, waiting to be written into its version_text.
  std::vector<std::string> dumpports_commands;

  // §21.7.3.1: scope names supplied to $dumpports must be unique across every
  // call. Records the scope and returns false when it repeats one already used
  // by an earlier $dumpports call.
  bool RegisterDumpportsScope(const std::string& scope);
  // §21.7.3.1: an explicitly named $dumpports output file may not be named by
  // more than one call. Records the name and returns false on a repeat.
  bool RegisterDumpportsFile(const std::string& file);
  // §21.7.3.7: an extended VCD control task may name the $dumpports output it
  // targets; the name matches only when some $dumpports call explicitly
  // specified that file. Returns true when the name was so registered.
  bool IsDumpportsFile(const std::string& file) const;
  // §21.7.3.7: true once at least one $dumpports call has explicitly named an
  // output file, so a control task's filename can be matched against the set.
  bool HasDumpportsFiles() const { return !dumpports_files.empty(); }
  // §21.7.4.1 (Syntax 21-27): an extended file's version_text lists the
  // $dumpports commands that produced it, so each call's source spelling is
  // recorded as it executes. A call made before the extended dump was opened
  // is held until the open replays it into the header; one made after goes
  // straight to the writer, which is holding its declaration commands for
  // exactly this.
  void AddDumpportsCommand(std::string text);

  // §21.7.3.1: $dumpports may be invoked many times, but the execution of all
  // $dumpports tasks shall be at the same simulation time. The first call
  // records its time; a later call passes only when it matches.
  bool RegisterDumpportsTime(uint64_t time);
  // §21.7.1.2: $dumpvars may be invoked as often as desired, but the execution
  // of all the $dumpvars tasks shall be at the same simulation time. The first
  // call records its time; a later call passes only when it matches. Separate
  // from RegisterDumpportsTime because §21.7.1.2 and §21.7.3.1 are two rules
  // over two sets of calls, and a source may call only one of the two tasks.
  bool RegisterDumpvarsTime(uint64_t time);

  // §21.7.5 (Table 21-11): record the declared SystemVerilog data type of a
  // dumped variable so its $var declaration can masquerade as the matching
  // IEEE Std 1364-2005 var_type. `kind` is the effective type keyword the
  // lowerer resolved for VCD -- a typed enum is already reduced to its base
  // type and a packed structure to a reg-vector masquerade. A variable with no
  // recorded kind reports kImplicit, which keeps the §21.7.2.3 net default.
  void SetVcdVarKind(std::string_view name, DataTypeKind kind);
  DataTypeKind GetVcdVarKind(std::string_view name) const;
  // §21.7.4.3.1: the declared direction of each dumped port, which is what
  // picks the list its extended VCD state characters come from. A name no port
  // declaration covers answers kNone, the unknown-direction list.
  void SetVcdPortDirection(std::string_view name, Direction direction);
  Direction GetVcdPortDirection(std::string_view name) const;

 private:
  // §21.7.3.1: the one simulation time at which every $dumpports call must
  // execute, recorded by the first call.
  bool have_dumpports_time_ = false;
  uint64_t dumpports_time_ = 0;
  // §21.7.1.2: the one simulation time at which every $dumpvars call must
  // execute, recorded by the first call.
  bool have_dumpvars_time_ = false;
  uint64_t dumpvars_time_ = 0;

  // §21.7.5 (Table 21-11): declared type keyword (enum base / packed struct
  // already resolved) of each dumped variable, consulted when its $var
  // declaration is written to pick the masquerading 1364-2005 var_type.
  std::unordered_map<std::string_view, DataTypeKind> var_kinds_;
  // §21.7.4.3.1: declared direction of each dumped port. See
  // GetVcdPortDirection.
  std::unordered_map<std::string_view, Direction> port_dirs_;
};

}  // namespace delta
