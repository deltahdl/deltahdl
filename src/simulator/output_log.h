#pragma once

// The standard output of a simulation run and the log file that copies it.
//
// Annex D.7 has the log file hold a copy of all the text printed to the
// standard output, with $nolog turning the copy off and $log turning it back
// on, and a file name argument to $log closing the log file open, creating the
// named one and directing the copy there. The clause is informative and names
// no default log file, so the copy begins when a $log names one; until then
// the two tasks only set whether the copy is enabled, which is what a log file
// named later starts under. D.7 also allows the file to open with the host
// command that ran the tool, which this log does not write.
//
// The copy is kept by owning the stream the simulator prints its standard
// output through: what is written to Out() reaches std::cout, whatever buffer
// std::cout stands on at the time, and while a log file is open and enabled it
// reaches the log file as well. Text a system task prints to the C stdout
// instead -- a §21.3 file output task given the STDOUT descriptor -- is handed
// to Copy so the log holds it too.

#include <fstream>
#include <ostream>
#include <streambuf>
#include <string>
#include <string_view>

namespace delta {

class OutputLog {
 public:
  OutputLog();

  // The stream standard output is printed through.
  std::ostream& Out() { return out_; }

  // $log("filename"): closes the open log file, creates the named one, and
  // directs the copy there, enabling it. A name the host cannot open leaves no
  // log file open, and the copy then goes nowhere until one is.
  void Open(std::string_view name);

  // $log and $nolog without a file name.
  void Enable() { enabled_ = true; }
  void Disable() { enabled_ = false; }
  bool Enabled() const { return enabled_; }

  // The name the last $log with an argument gave, empty when none has.
  const std::string& Name() const { return name_; }

  // Writes `text` to the log file when one is open and the copy is enabled.
  // Out() calls it for everything written through the stream; a task that
  // prints to the standard output by another route calls it itself. Every
  // write is flushed, since the log is read by whoever runs the tool while it
  // still runs.
  void Copy(std::string_view text);

 private:
  // The stream buffer behind Out(): forwards each write to std::cout and to
  // Copy, and a flush to std::cout.
  class TeeBuf : public std::streambuf {
   public:
    explicit TeeBuf(OutputLog& log) : log_(log) {}

   protected:
    int_type overflow(int_type ch) override;
    std::streamsize xsputn(const char* s, std::streamsize n) override;
    int sync() override;

   private:
    OutputLog& log_;
  };

  TeeBuf buf_;
  std::ostream out_;
  std::ofstream file_;
  std::string name_;
  bool enabled_ = true;
};

}  // namespace delta
