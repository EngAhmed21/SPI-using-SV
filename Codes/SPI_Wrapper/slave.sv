module slave(
	input logic SS_n, MOSI, 
	slave_RAM_intf.SLAVE SR_intf,
	output logic MISO
);
	localparam MEM_DEPTH = SR_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	typedef enum bit [2 : 0] {IDLE, CHK_CMD, WRITE, READ_ADD, READ_DATA} STATE_e;

	logic clk, rst_n, tx_valid, rx_valid;
	logic [ADDR_SIZE - 1 : 0] tx_data;
	logic [ADDR_SIZE + 1 : 0] rx_data;

	logic rd_flag, rx_valid_in_RD, MISO_int;
	logic [$clog2(ADDR_SIZE) : 0] count_tx, count_rx;
	logic [ADDR_SIZE + 1 : 0] bus_rx;

	STATE_e cs, ns;

	assign clk 					= SR_intf.clk;
	assign rst_n 				= SR_intf.rst_n;
	assign tx_valid 			= SR_intf.tx_valid;
	assign tx_data 				= SR_intf.tx_data;
	assign SR_intf.rx_valid 	= rx_valid;
	assign SR_intf.rx_data 		= rx_data;

	// rd_flag
	always @(posedge clk, negedge rst_n) begin
        if (!rst_n)
            rd_flag <= 0;
        else if ((cs == READ_ADD)  && (count_rx == 0))
            rd_flag <= 1;
        else if ((cs == READ_DATA) && (count_tx == 0))
            rd_flag <= 0;
    end

	// next state logic
	always @(*) begin
		case(cs)
			IDLE: 		ns = (SS_n) ? IDLE : CHK_CMD;
			CHK_CMD: 
				if(SS_n) 
					ns = IDLE;
				else if (!MOSI)
					ns = WRITE;
				else
					if (!rd_flag) 
						ns = READ_ADD;
					else
						ns = READ_DATA;
			WRITE:		ns = (SS_n) ? IDLE : WRITE;	 
			READ_ADD:   ns = (SS_n) ? IDLE : READ_ADD;
			READ_DATA:  ns = (SS_n) ? IDLE : READ_DATA;
			default:    ns = IDLE;
		endcase
	end

	// current state memory
	always @(posedge clk, negedge rst_n) begin
		if (!rst_n) 
			cs <= IDLE;
		else 
			cs <= ns;
	end 

	// rx
	always @(posedge clk, negedge rst_n) begin
		if ((!rst_n) || (cs == IDLE)) begin
			count_rx <= ADDR_SIZE + 2;
			bus_rx   <= 0;
		end
		else if (((cs == WRITE) || (cs == READ_ADD) || (cs == READ_DATA)) && (count_rx != 0)) begin
			bus_rx [count_rx - 1] <= MOSI;
			count_rx <= count_rx - 1;
		end
	end

	// tx
	always @(posedge clk, negedge rst_n) begin
		if ((!rst_n) || (cs == IDLE)) begin
			count_tx <= ADDR_SIZE;
			MISO_int   <= 0;
		end
		else if ((cs == READ_DATA) && (tx_valid) && (count_rx == 0) && (count_tx != 0)) begin
			MISO_int <= tx_data [count_tx - 1];
			count_tx <= count_tx - 1;
		end
	end

	// rx_valid_in_RD: to ensure that rx_valid is high for only one clock 
	always @(posedge clk, negedge rst_n) begin
        if ((!rst_n) || (count_rx == (ADDR_SIZE + 2)))
            rx_valid_in_RD <= 0;
        else if (count_rx == 0)
            rx_valid_in_RD <= 1;
    end

	// outputs
	assign rx_valid = (((cs == WRITE) || (cs == READ_ADD) || ((cs == READ_DATA) && (!rx_valid_in_RD))) && (count_rx == 0));
	assign rx_data  = bus_rx;
	assign MISO     = MISO_int;

	// Assertions for the internal signals
	`ifdef SIM_SLAVE 
		// Check reset values
		always_comb begin
			if (!rst_n) begin
				sl_rst_count_rx_a:	assert final (count_rx == ADDR_SIZE + 2);
				sl_rst_count_tx_a:	assert final (count_tx == ADDR_SIZE);
				sl_rst_cs_a:		assert final (cs == IDLE);
				sl_rst_rd_flag_a:	assert final (rd_flag == 0);
			end
		end

		// cs
		property sl_cs_idle_pr;
			@(posedge clk) disable iff(!rst_n) (SS_n) |=> (cs == IDLE);
		endproperty
		sl_cs_idle_a:	  assert property (sl_cs_idle_pr);
		sl_cs_idle_cov:   cover  property (sl_cs_idle_pr);

		property sl_cs_chk_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == IDLE) && (!SS_n)) |=> (cs == CHK_CMD);
		endproperty
		sl_cs_chk_a:	  assert property (sl_cs_chk_pr);
		sl_cs_chk_cov:    cover  property (sl_cs_chk_pr);

		property sl_cs_wr_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == CHK_CMD) && (!SS_n) && (!MOSI)) |=> (cs == WRITE);
		endproperty
		sl_cs_wr_a:	  	 assert property (sl_cs_wr_pr);
		sl_cs_wr_cov:    cover  property (sl_cs_wr_pr);

		property sl_cs_ra_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == CHK_CMD) && (!SS_n) && (MOSI) && (!rd_flag)) |=> (cs == READ_ADD);
		endproperty
		sl_cs_ra_a:	  	 assert property (sl_cs_ra_pr);
		sl_cs_ra_cov:    cover  property (sl_cs_ra_pr);

		property sl_cs_rd_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == CHK_CMD) && (!SS_n) && (MOSI) && (rd_flag)) |=> (cs == READ_DATA);
		endproperty
		sl_cs_rd_a:	  	 assert property (sl_cs_rd_pr);
		sl_cs_rd_cov:    cover  property (sl_cs_rd_pr);

		// read data flag
		property sl_rd_flag_ra_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == READ_ADD) && (count_rx == 0)) |=> (rd_flag);
		endproperty
		sl_rd_flag_ra_a:	   assert property (sl_rd_flag_ra_pr);
		sl_rd_flag_ra_cov:     cover  property (sl_rd_flag_ra_pr);

		property sl_rd_flag_rd_pr;
			@(posedge clk) disable iff(!rst_n) ((cs == READ_ADD) && (count_tx == 0)) |=> (!rd_flag);
		endproperty
		sl_rd_flag_rd_a:	   assert property (sl_rd_flag_rd_pr);
		sl_rd_flag_rd_cov:     cover  property (sl_rd_flag_rd_pr);
	`endif 
endmodule