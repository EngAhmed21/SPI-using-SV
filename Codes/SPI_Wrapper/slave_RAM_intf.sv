interface slave_RAM_intf #(parameter MEM_DEPTH = 256) (input clk);
    localparam ADDR_SIZE = $clog2(MEM_DEPTH);

    logic rst_n, rx_valid, tx_valid;
    logic [ADDR_SIZE + 1 : 0] rx_data;
    logic [ADDR_SIZE - 1 : 0] tx_data;

    modport RAM (
    input  clk, rst_n, rx_valid, rx_data,
    output tx_data, tx_valid
    );

    modport SLAVE (
    input  clk, rst_n, tx_valid, tx_data,
    output rx_data, rx_valid
    );

    modport RAM_test (
    input  clk, tx_data, tx_valid,
    output rst_n, rx_valid, rx_data
    );

    modport SLAVE_test (
    input  clk, rx_data, rx_valid,
    output rst_n, tx_valid, tx_data
    );
endinterface //SPI_intf