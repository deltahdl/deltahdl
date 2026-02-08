#pragma once

#include <string>
#include <vector>

namespace delta {

// --- Built-in system tasks (IEEE 1800-2023 section 21) ---

void exec_display(const std::vector<std::string>& args);
void exec_write(const std::vector<std::string>& args);
void exec_finish();
void exec_stop();

// --- Format string processing ---
// Supports: %d (decimal), %h/%x (hex), %b (binary), %s (string), %t (time)

std::string format_args(const std::vector<std::string>& args);

}  // namespace delta
