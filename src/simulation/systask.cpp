#include "simulation/systask.h"

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <string>

namespace delta {

// --- Format helpers (defined before use) ---

static bool is_format_spec(char c) {
    return c == 'd' || c == 'h' || c == 'x' || c == 'b' || c == 's' || c == 't';
}

static std::string format_single_value(char spec, unsigned long long num) {
    char buf[128];
    switch (spec) {
    case 'd':
        std::snprintf(buf, sizeof(buf), "%llu", num);
        return buf;
    case 'h':
    case 'x':
        std::snprintf(buf, sizeof(buf), "%llx", num);
        return buf;
    case 'b': {
        if (num == 0)
            return "0";
        std::string result;
        for (auto tmp = num; tmp > 0; tmp >>= 1) {
            result.insert(result.begin(), (tmp & 1) ? '1' : '0');
        }
        return result;
    }
    default:
        std::snprintf(buf, sizeof(buf), "%llu", num);
        return buf;
    }
}

static std::string apply_format(char spec, const std::string& val) {
    if (spec == 's' || spec == 't') {
        return val;
    }

    unsigned long long num = 0;
    if (!val.empty()) {
        try {
            num = std::stoull(val, nullptr, 0);
        } catch (...) {
            return val;
        }
    } else {
        return val;
    }

    return format_single_value(spec, num);
}

static bool try_format_escape(const std::string& fmt, size_t& i,
                              const std::vector<std::string>& args, size_t& arg_idx,
                              std::string& result) {
    if (fmt[i] != '%') {
        return false;
    }
    if (i + 1 >= fmt.size()) {
        return false;
    }

    char next = fmt[i + 1];
    if (next == '%') {
        result.push_back('%');
        ++i;
        return true;
    }

    if (!is_format_spec(next)) {
        return false;
    }

    if (arg_idx < args.size()) {
        result.append(apply_format(next, args[arg_idx]));
        ++arg_idx;
    }
    ++i;
    return true;
}

// --- Format string processing ---

std::string format_args(const std::vector<std::string>& args) {
    if (args.empty()) {
        return {};
    }

    const std::string& fmt = args[0];
    std::string result;
    result.reserve(fmt.size() * 2);
    size_t arg_idx = 1;

    for (size_t i = 0; i < fmt.size(); ++i) {
        if (!try_format_escape(fmt, i, args, arg_idx, result)) {
            result.push_back(fmt[i]);
        }
    }

    return result;
}

// --- System task implementations ---

void exec_display(const std::vector<std::string>& args) {
    std::string text = format_args(args);
    std::cout << text << '\n';
}

void exec_write(const std::vector<std::string>& args) {
    std::string text = format_args(args);
    std::cout << text;
}

void exec_finish() {
    std::exit(0);
}

void exec_stop() {
    // In a full simulator this would drop to an interactive prompt.
    // For now, print a message and pause via stdin.
    std::cout << "Simulation stopped. Press Enter to continue...\n";
    std::cin.get();
}

} // namespace delta
