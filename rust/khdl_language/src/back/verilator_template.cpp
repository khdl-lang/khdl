#include <cstdint>
#include <iostream>
#include <memory>

#include "verilated.h"
#if VM_TRACE
#include "verilated_vcd_c.h"
#endif
#include "/*[TEMPLATE_TOP_CLASS_NAME]*/.h"

typedef uint8_t Result;
const Result SUCCESS = 0;
const Result FAIL_CHECK = 1;
const Result FAIL_WRONG_LEN = 2;
const Result FAIL_DATA_NULL = 3;
const Result FAIL_INVALID_PORT = 4;
const Result FINISH = 16;

// Port get/set glue functions.
template <typename T>
void int_to_bytes(T value, uint8_t *data) {
    for (size_t i = 0; i < sizeof(T); ++i) {
        data[i] = (value >> (i * 8)) & 0xFF;
    }
}
template <typename T>
T int_from_bytes(const uint8_t *data) {
    T result = 0;
    for (size_t i = 0; i < sizeof(T); ++i) {
        result |= (static_cast<T>(data[i]) << (i * 8));
    }
    return result;
}

template <typename T>
Result get_port_primitive(T port, size_t data_len, uint8_t *data) {
    size_t expected_len = sizeof(port);
    if (data_len != expected_len) return FAIL_WRONG_LEN;
    if (!data) return FAIL_DATA_NULL;
    int_to_bytes(port, data);
    return SUCCESS;
}

Result get_port_impl(uint8_t port, size_t data_len, uint8_t *data) {
    return get_port_primitive(port, data_len, data);
}
Result get_port_impl(uint16_t port, size_t data_len, uint8_t *data) {
    return get_port_primitive(port, data_len, data);
}
Result get_port_impl(uint32_t port, size_t data_len, uint8_t *data) {
    return get_port_primitive(port, data_len, data);
}
Result get_port_impl(uint64_t port, size_t data_len, uint8_t *data) {
    return get_port_primitive(port, data_len, data);
}
template <size_t W>
Result get_port_impl(VlWide<W> &port, size_t data_len, uint8_t *data) {
    size_t expected_len = W * sizeof(EData);
    if (data_len != expected_len) return FAIL_WRONG_LEN;
    if (!data) return FAIL_DATA_NULL;
    for (size_t i = 0; i < W; ++i) {
        int_to_bytes<EData>(port.at(i), &data[i * sizeof(EData)]);
    }
    return SUCCESS;
}

template <typename T>
Result set_port_primitive(T &port, size_t data_len, uint8_t const *data) {
    size_t expected_len = sizeof(port);
    if (data_len != expected_len) return FAIL_WRONG_LEN;
    if (!data) return FAIL_DATA_NULL;
    port = int_from_bytes<T>(data);
    return SUCCESS;
}

Result set_port_impl(uint8_t &port, size_t data_len, uint8_t const *data) {
    return set_port_primitive(port, data_len, data);
}
Result set_port_impl(uint16_t &port, size_t data_len, uint8_t const *data) {
    return set_port_primitive(port, data_len, data);
}
Result set_port_impl(uint32_t &port, size_t data_len, uint8_t const *data) {
    return set_port_primitive(port, data_len, data);
}
Result set_port_impl(uint64_t &port, size_t data_len, uint8_t const *data) {
    return set_port_primitive(port, data_len, data);
}
template <size_t W>
Result set_port_impl(VlWide<W> &port, size_t data_len, uint8_t const *data) {
    size_t expected_len = W * sizeof(EData);
    if (data_len != expected_len) return FAIL_WRONG_LEN;
    if (!data) return FAIL_DATA_NULL;

    for (size_t i = 0; i < W; ++i) {
        port.data()[i] = int_from_bytes<EData>(&data[i * sizeof(EData)]);
    }
    return SUCCESS;
}

// TODO rename to instance
// The wrapper instance returned and operated on by the C API.
class Wrapper {
   public:
    VerilatedContext *context;
    /*[TEMPLATE_TOP_CLASS_NAME]*/ *top;
#if VM_TRACE
    VerilatedVcdC *trace = nullptr;
#endif

    Wrapper(char *trace_path) : context(new VerilatedContext()), top(new /*[TEMPLATE_TOP_CLASS_NAME]*/(context)) {
#if VM_TRACE
        if (trace_path) {
            context->traceEverOn(true);
            trace = new VerilatedVcdC();
            top->trace(trace, 1024);
            trace->open(trace_path);
        }
#endif
    }

    ~Wrapper() {
#if VM_TRACE
        delete trace;
#endif
        delete top;
        delete context;
    }
};

// TODO for verilator, generate an extra wrapper layer
//     that prefixes all ports so they never conflict with any builtin
//     properties
extern "C" {
    uint64_t check_hash() {
        return /*[TEMPLATE_CHECK_HASH]*/;
    }

    bool trace_supported() {
        return VM_TRACE;
    }

    Wrapper *create_instance(char *trace_path) {
        return new Wrapper(trace_path);
    }

    void destroy_instance(Wrapper *wrapper) {
        // TODO final code somewhere?
        // wrapper->top.final();
        // wrapper->context.statsPrintSummary();

        delete wrapper;
    }

    Result step(Wrapper *wrapper, uint64_t increment_time) {
        if (wrapper->context->gotFinish()) {
            return FINISH;
        }

        wrapper->context->timeInc(increment_time);
        wrapper->top->eval();

#if VM_TRACE
        if (wrapper->trace) {
            wrapper->trace->dump(wrapper->context->time());
        }
#endif

        return SUCCESS;
    }

    void save_trace(Wrapper *wrapper) {
#if VM_TRACE
        if (wrapper->trace) {
            wrapper->trace->close();
            delete wrapper->trace;
            wrapper->trace = nullptr;
        }
#endif
    }

    Result get_port(Wrapper *wrapper, uint32_t port_index, size_t data_len, uint8_t *data) {
        // clang-format off
        switch (port_index) {
            /*[TEMPLATE_PORTS_GET]*/
            default: return FAIL_INVALID_PORT;
        }
        // clang-format on
    }

    Result set_port(Wrapper *wrapper, uint32_t port_index, size_t data_len, uint8_t const *data) {
        // TODO check somewhere that sync signals only change on the right edges?
        // clang-format off
        switch (port_index) {
            /*[TEMPLATE_PORTS_SET]*/
            default: return FAIL_INVALID_PORT;
        }
        // clang-format on
    }
}
