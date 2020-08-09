/**
  *
  * testbench.v
  *
  */
  
`include "bsg_noc_links.vh"

module testbench
 import bp_common_pkg::*;
 import bp_common_aviary_pkg::*;
 import bp_be_pkg::*;
 import bp_common_rv64_pkg::*;
 import bp_cce_pkg::*;
 import bp_me_pkg::*;
 import bp_common_cfg_link_pkg::*;
 import bsg_noc_pkg::*;
 #(parameter bp_params_e bp_params_p = BP_CFG_FLOWVAR // Replaced by the flow with a specific bp_cfg
   `declare_bp_proc_params(bp_params_p)
   `declare_bp_fe_be_if_widths(vaddr_width_p, paddr_width_p, asid_width_p, branch_metadata_fwd_width_p)
   `declare_bp_me_if_widths(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p)

   // Tracing parameters
   , parameter calc_trace_p                = 0
   , parameter cce_trace_p                 = 0
   , parameter cmt_trace_p                 = 0
   , parameter dram_trace_p                = 0
   , parameter npc_trace_p                 = 0
   , parameter icache_trace_p              = 0
   , parameter dcache_trace_p              = 0
   , parameter vm_trace_p                  = 0
   , parameter core_profile_p              = 0
   , parameter preload_mem_p               = 0
   , parameter load_nbf_p                  = 0
   , parameter skip_init_p                 = 0
   , parameter cosim_p                     = 0
   , parameter cosim_cfg_file_p            = "prog.cfg"
   , parameter cosim_instr_p               = 0
   , parameter warmup_instr_p              = 0

   , parameter mem_zero_p         = 1
   , parameter mem_file_p         = "prog.mem"
   , parameter mem_cap_in_bytes_p = 2**28
   , parameter [paddr_width_p-1:0] mem_offset_p = dram_base_addr_gp

   // Number of elements in the fake BlackParrot memory
   , parameter use_max_latency_p      = 0
   , parameter use_random_latency_p   = 0
   , parameter use_dramsim2_latency_p = 0

   , parameter max_latency_p = 15

   , parameter dram_clock_period_in_ps_p = `BP_SIM_CLK_PERIOD
   , parameter dram_cfg_p                = "dram_ch.ini"
   , parameter dram_sys_cfg_p            = "dram_sys.ini"
   , parameter dram_capacity_p           = 16384
   )
  (input clk_i
   , input reset_i
   );

`declare_bp_me_if(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p)

initial begin
  if (num_core_p > 1) begin
    assert (cosim_p == 0) else $error("cosim_p not supported for num_core_p > 1");
  end
end

logic [num_core_p-1:0] program_finish_lo;
logic cosim_finish_lo;

bp_cce_mem_msg_s proc_mem_cmd_lo;
logic proc_mem_cmd_v_lo, proc_mem_cmd_ready_li;
bp_cce_mem_msg_s proc_mem_resp_li;
logic proc_mem_resp_v_li, proc_mem_resp_yumi_lo;

bp_cce_mem_msg_s a_proc_mem_cmd_lo;
logic a_proc_mem_cmd_v_lo, a_proc_mem_cmd_yumi_li;
bp_cce_mem_msg_s a_proc_mem_resp_li;
logic a_proc_mem_resp_v_li, a_proc_mem_resp_ready_lo;

bp_cce_mem_msg_s b_proc_mem_cmd_lo;
logic b_proc_mem_cmd_v_lo, b_proc_mem_cmd_ready_li;
bp_cce_mem_msg_s b_proc_mem_resp_li;
logic b_proc_mem_resp_v_li, b_proc_mem_resp_yumi_lo;

bp_cce_mem_msg_s nbf_proc_mem_cmd_lo;
logic nbf_proc_mem_cmd_v_lo, nbf_proc_mem_cmd_yumi_li;
bp_cce_mem_msg_s nbf_proc_mem_resp_li;
logic nbf_proc_mem_resp_v_li, nbf_proc_mem_resp_ready_lo;

bp_cce_mem_msg_s proc_io_cmd_lo;
logic proc_io_cmd_v_lo, proc_io_cmd_ready_li;
bp_cce_mem_msg_s proc_io_resp_li;
logic proc_io_resp_v_li, proc_io_resp_yumi_lo;

bp_cce_mem_msg_s io_cmd_lo;
logic io_cmd_v_lo, io_cmd_ready_li;
bp_cce_mem_msg_s io_resp_li;
logic io_resp_v_li, io_resp_yumi_lo;

bp_cce_mem_msg_s nbf_cmd_lo;
logic nbf_cmd_v_lo, nbf_cmd_yumi_li;
bp_cce_mem_msg_s nbf_resp_li;
logic nbf_resp_v_li, nbf_resp_ready_lo;

bp_cce_mem_msg_s cfg_cmd_lo;
logic cfg_cmd_v_lo, cfg_cmd_yumi_li;
bp_cce_mem_msg_s cfg_resp_li;
logic cfg_resp_v_li, cfg_resp_ready_lo;

bp_cce_mem_msg_s load_cmd_lo;
logic load_cmd_v_lo, load_cmd_yumi_li;
bp_cce_mem_msg_s load_resp_li;
logic load_resp_v_li, load_resp_ready_lo;

wrapper
 #(.bp_params_p(bp_params_p))
 wrapper
  (.clk_i(clk_i)
   ,.reset_i(reset_i)

   ,.io_cmd_o(proc_io_cmd_lo)
   ,.io_cmd_v_o(proc_io_cmd_v_lo)
   ,.io_cmd_ready_i(proc_io_cmd_ready_li)

   ,.io_resp_i(proc_io_resp_li)
   ,.io_resp_v_i(proc_io_resp_v_li)
   ,.io_resp_yumi_o(proc_io_resp_yumi_lo)

   ,.io_cmd_i(load_cmd_lo)
   ,.io_cmd_v_i(load_cmd_v_lo)
   ,.io_cmd_yumi_o(load_cmd_yumi_li)

   ,.io_resp_o(load_resp_li)
   ,.io_resp_v_o(load_resp_v_li)
   ,.io_resp_ready_i(load_resp_ready_lo)

   ,.mem_cmd_o(b_proc_mem_cmd_lo)
   ,.mem_cmd_v_o(b_proc_mem_cmd_v_lo)
   ,.mem_cmd_ready_i(b_proc_mem_cmd_ready_li)

   ,.mem_resp_i(b_proc_mem_resp_li)
   ,.mem_resp_v_i(b_proc_mem_resp_v_li)
   ,.mem_resp_yumi_o(b_proc_mem_resp_yumi_lo)
   );

wire proc_mem_init_done_lo;
wire dmc_refresh_lo;

/*
  logic [31:0] xui_cycle_r;
  logic xui_node_done_lo;

  bsg_counter_clear_up 
 #(.max_val_p (64'(1<<32-1))
  ,.init_val_p(0)
  ) xui_cycle
  (.clk_i     (clk_i)
  ,.reset_i   (~proc_mem_init_done_lo)
  ,.clear_i   (1'b0)
  ,.up_i      (~xui_node_done_lo)
  ,.count_o   (xui_cycle_r)
  );
*/
if (load_nbf_p & preload_mem_p)
  begin: lpddr
  
  logic dfi_clk_lo, axi_clk_lo, axi_reset_lo;
  bsg_nonsynth_clock_gen 
 #(.cycle_time_p(`BP_SIM_CLK_PERIOD*5))
  dfi_clkgen 
  (.o(dfi_clk_lo));
  bsg_nonsynth_clock_gen 
 #(.cycle_time_p(`BP_SIM_CLK_PERIOD/5))
  axi_clkgen 
  (.o(axi_clk_lo));
  bsg_sync_sync #(.width_p(1)) axi_reset
  (.oclk_i      ( axi_clk_lo   )
  ,.iclk_data_i ( reset_i      )
  ,.oclk_data_o ( axi_reset_lo ));
  
  // DMC
  //localparam ui_addr_width_p = paddr_width_p; // word address (1 TB)
  //localparam ui_data_width_p = dword_width_p;
  //localparam burst_data_width_p = cce_block_width_p;
  localparam dq_data_width_p = 32;
  //localparam dq_group_lp = dq_data_width_p >> 3;
  localparam axi_id_width_p = 6;
  localparam axi_addr_width_p = 64;
  localparam axi_data_width_p = 256;
  localparam axi_burst_len_p = 2;
  localparam axi_mem_els_p = 16777216; // 2 * 2 Gb
  localparam axi_strb_width_lp = axi_data_width_p >> 3;
  
  localparam dmc_addr_width_gp = 28;
  localparam dmc_data_width_gp = 32;
  localparam dmc_cmd_afifo_depth_gp = 4;
  localparam dmc_cmd_sfifo_depth_gp = 4;
  localparam clk_gen_num_adgs_gp = 1;

  wire                              app_en_lo;
  wire                              app_rdy_li;
  wire                        [2:0] app_cmd_lo;
  wire          [paddr_width_p-1:0] app_addr_lo;
  wire      [dmc_addr_width_gp-1:0] app_addr_li = app_addr_lo[2+:dmc_addr_width_gp];

  wire                              app_wdf_wren_lo;
  wire                              app_wdf_rdy_li;
  wire      [cce_block_width_p-1:0] app_wdf_data_lo;
  wire [(cce_block_width_p>>3)-1:0] app_wdf_mask_lo;
  wire                              app_wdf_end_lo;

  wire                              app_rd_data_valid_li;
  wire      [cce_block_width_p-1:0] app_rd_data_li;
  wire                              app_rd_data_end_li;

  wire                              axi_awready;
  wire         [axi_id_width_p-1:0] axi_awid;
  wire       [axi_addr_width_p-1:0] axi_awaddr;
  wire                              axi_awvalid;
  wire                              axi_wready;
  wire       [axi_data_width_p-1:0] axi_wdata;
  wire      [axi_strb_width_lp-1:0] axi_wstrb;
  wire                              axi_wlast;
  wire                              axi_wvalid;
  wire         [axi_id_width_p-1:0] axi_bid;
  wire                        [1:0] axi_bresp;
  wire                              axi_bvalid;
  wire                              axi_bready;
  wire                              axi_arready;
  wire         [axi_id_width_p-1:0] axi_arid;
  wire       [axi_addr_width_p-1:0] axi_araddr;
  wire                              axi_arvalid;
  wire         [axi_id_width_p-1:0] axi_rid;
  wire       [axi_data_width_p-1:0] axi_rdata;
  wire                        [1:0] axi_rresp;
  wire                              axi_rlast;
  wire                              axi_rvalid;
  wire                              axi_rready;

  bp_me_cce_to_xui
   #(.bp_params_p(bp_params_p)
     ,.flit_width_p(mem_noc_flit_width_p)
     ,.cord_width_p(mem_noc_cord_width_p)
     ,.cid_width_p(mem_noc_cid_width_p)
     ,.len_width_p(mem_noc_len_width_p)
     )
   dmc_link
    (.clk_i(clk_i)
     ,.reset_i(reset_i)

     ,.mem_cmd_i(proc_mem_cmd_lo)
     ,.mem_cmd_v_i(proc_mem_cmd_v_lo)
     ,.mem_cmd_ready_o(proc_mem_cmd_ready_li)

     ,.mem_resp_o(proc_mem_resp_li)
     ,.mem_resp_v_o(proc_mem_resp_v_li)
     ,.mem_resp_yumi_i(proc_mem_resp_yumi_lo)

     ,.app_addr_o(app_addr_lo)
     ,.app_cmd_o(app_cmd_lo)
     ,.app_en_o(app_en_lo)
     ,.app_rdy_i(app_rdy_li)
     ,.app_wdf_wren_o(app_wdf_wren_lo)
     ,.app_wdf_data_o(app_wdf_data_lo)
     ,.app_wdf_mask_o(app_wdf_mask_lo)
     ,.app_wdf_end_o(app_wdf_end_lo)
     ,.app_wdf_rdy_i(app_wdf_rdy_li)
     ,.app_rd_data_valid_i(app_rd_data_valid_li)
     ,.app_rd_data_i(app_rd_data_li)
     ,.app_rd_data_end_i(app_rd_data_end_li)
     );

/*
  bsg_xui_stress_test_node
   #(.addr_width_p(paddr_width_p)
    ,.data_width_p(cce_block_width_p)
    ,.num_requests_p(5000)
    ,.nonblock_read_p(1)
     )
   xui_node
    (.clk_i(clk_i)
     ,.reset_i(~proc_mem_init_done_lo)
     ,.done_o(xui_node_done_lo)

     ,.app_addr_o(app_addr_lo)
     ,.app_cmd_o(app_cmd_lo)
     ,.app_en_o(app_en_lo)
     ,.app_rdy_i(app_rdy_li)
     ,.app_wdf_wren_o(app_wdf_wren_lo)
     ,.app_wdf_data_o(app_wdf_data_lo)
     ,.app_wdf_mask_o(app_wdf_mask_lo)
     ,.app_wdf_end_o(app_wdf_end_lo)
     ,.app_wdf_rdy_i(app_wdf_rdy_li)
     ,.app_rd_data_valid_i(app_rd_data_valid_li)
     ,.app_rd_data_i(app_rd_data_li)
     ,.app_rd_data_end_i(app_rd_data_end_li)
     );
*/
  import bsg_dmc_pkg::bsg_dmc_s;
  bsg_dmc_s dmc_p;

  assign dmc_p.trefi        = 16'h03ff;
  assign dmc_p.tmrd         = 4'h1;
  assign dmc_p.trfc         = 4'hf;
  assign dmc_p.trc          = 4'ha;
  assign dmc_p.trp          = 4'h3;
  assign dmc_p.tras         = 4'h7;
  assign dmc_p.trrd         = 4'h1;
  assign dmc_p.trcd         = 4'h2;
  assign dmc_p.twr          = 4'hb;
  assign dmc_p.twtr         = 4'h7;
  assign dmc_p.trtp         = 4'h8;
  assign dmc_p.tcas         = 4'h3;
  assign dmc_p.col_width    = 4'hb;
  assign dmc_p.row_width    = 4'he;
  assign dmc_p.bank_width   = 2'h2;
  assign dmc_p.dqs_sel_cal  = 3'h0;
  assign dmc_p.init_cycles  = 16'h9c4a;
  assign dmc_p.bank_pos     = 6'h19;

  wire   dmc_sys_reset_li   = reset_i;
  
  bsg_dmc_emulator #
    (.num_adgs_p            ( clk_gen_num_adgs_gp )
    ,.ui_addr_width_p       ( dmc_addr_width_gp   )
    ,.ui_data_width_p       ( cce_block_width_p   )
    ,.burst_data_width_p    ( cce_block_width_p   )
    ,.dq_data_width_p       ( dmc_data_width_gp   )
    ,.cmd_afifo_depth_p     ( dmc_cmd_afifo_depth_gp )
    ,.cmd_sfifo_depth_p     ( dmc_cmd_sfifo_depth_gp )
    ,.axi_id_width_p        ( axi_id_width_p      )
    ,.axi_addr_width_p      ( axi_addr_width_p    )
    ,.axi_data_width_p      ( axi_data_width_p    )
    ,.axi_burst_len_p       ( axi_burst_len_p     ))
  dmc
    (.dmc_p_i               ( dmc_p                )
    ,.sys_reset_i           ( dmc_sys_reset_li     )

    // Application interface
    ,.app_addr_i            ( app_addr_li          )
    ,.app_cmd_i             ( app_cmd_lo           )
    ,.app_en_i              ( app_en_lo            )
    ,.app_rdy_o             ( app_rdy_li           )

    ,.app_wdf_wren_i        ( app_wdf_wren_lo      )
    ,.app_wdf_data_i        ( app_wdf_data_lo      )
    ,.app_wdf_mask_i        ( app_wdf_mask_lo      )
    ,.app_wdf_end_i         ( app_wdf_end_lo       )
    ,.app_wdf_rdy_o         ( app_wdf_rdy_li       )

    ,.app_rd_data_valid_o   ( app_rd_data_valid_li )
    ,.app_rd_data_o         ( app_rd_data_li       )
    ,.app_rd_data_end_o     ( app_rd_data_end_li   )

    // Stubbed compatibility ports
    ,.app_ref_req_i         ( 1'b0 )
    ,.app_ref_ack_o         ()
    ,.app_zq_req_i          ( 1'b0 )
    ,.app_zq_ack_o          ()
    ,.app_sr_req_i          ( 1'b0 )
    ,.app_sr_active_o       ()

    ,.init_calib_complete_o ( proc_mem_init_done_lo)
    ,.dmc_refresh_o         ( dmc_refresh_lo       )

    ,.ui_clk_i              ( clk_i                )
    ,.dfi_clk_1x_i          ( dfi_clk_lo           )

    ,.device_temp_o         (                      )
    
    ,.axi_clk_i             ( axi_clk_lo           )
    ,.axi_reset_i           ( axi_reset_lo         )
    ,.axi_fifo_error_o      (                      )

    ,.axi_awready_i         ( axi_awready          )
    ,.axi_awid_o            ( axi_awid             )
    ,.axi_awaddr_o          ( axi_awaddr           )
    ,.axi_awvalid_o         ( axi_awvalid          )
    ,.axi_awlen_o           (                      )
    ,.axi_awsize_o          (                      )
    ,.axi_awburst_o         (                      )
    ,.axi_awcache_o         (                      )
    ,.axi_awprot_o          (                      )
    ,.axi_awlock_o          (                      )
    ,.axi_wready_i          ( axi_wready           )
    ,.axi_wdata_o           ( axi_wdata            )
    ,.axi_wstrb_o           ( axi_wstrb            )
    ,.axi_wlast_o           ( axi_wlast            )
    ,.axi_wvalid_o          ( axi_wvalid           )
    ,.axi_bid_i             ( axi_bid              )
    ,.axi_bresp_i           ( axi_bresp            )
    ,.axi_bvalid_i          ( axi_bvalid           )
    ,.axi_bready_o          ( axi_bready           )
    ,.axi_arready_i         ( axi_arready          )
    ,.axi_arid_o            ( axi_arid             )
    ,.axi_araddr_o          ( axi_araddr           )
    ,.axi_arvalid_o         ( axi_arvalid          )
    ,.axi_arlen_o           (                      )
    ,.axi_arsize_o          (                      )
    ,.axi_arburst_o         (                      )
    ,.axi_arcache_o         (                      )
    ,.axi_arprot_o          (                      )
    ,.axi_arlock_o          (                      )
    ,.axi_rid_i             ( axi_rid              )
    ,.axi_rdata_i           ( axi_rdata            )
    ,.axi_rresp_i           ( axi_rresp            )
    ,.axi_rlast_i           ( axi_rlast            )
    ,.axi_rvalid_i          ( axi_rvalid           )
    ,.axi_rready_o          ( axi_rready           )
    );

    bsg_nonsynth_manycore_axi_mem #(
        .axi_id_width_p(axi_id_width_p)
        ,.axi_addr_width_p(axi_addr_width_p)
        ,.axi_data_width_p(axi_data_width_p)
        ,.axi_burst_len_p(axi_burst_len_p)
        ,.mem_els_p(axi_mem_els_p)
        ,.bsg_dram_included_p(1)
      ) axi_mem (
        .clk_i(axi_clk_lo)
        ,.reset_i(axi_reset_lo)

        ,.axi_awid_i(axi_awid)
        ,.axi_awaddr_i(axi_awaddr)
        ,.axi_awvalid_i(axi_awvalid)
        ,.axi_awready_o(axi_awready)

        ,.axi_wdata_i(axi_wdata)
        ,.axi_wstrb_i(axi_wstrb)
        ,.axi_wlast_i(axi_wlast)
        ,.axi_wvalid_i(axi_wvalid)
        ,.axi_wready_o(axi_wready)

        ,.axi_bid_o(axi_bid)
        ,.axi_bresp_o(axi_bresp)
        ,.axi_bvalid_o(axi_bvalid)
        ,.axi_bready_i(axi_bready)

        ,.axi_arid_i(axi_arid)
        ,.axi_araddr_i(axi_araddr)
        ,.axi_arvalid_i(axi_arvalid)
        ,.axi_arready_o(axi_arready)

        ,.axi_rid_o(axi_rid)
        ,.axi_rdata_o(axi_rdata)
        ,.axi_rresp_o(axi_rresp)
        ,.axi_rlast_o(axi_rlast)
        ,.axi_rvalid_o(axi_rvalid)
        ,.axi_rready_i(axi_rready)
      );
  
  end
else
  begin: bp_mem

bp_mem
 #(.bp_params_p(bp_params_p)
   ,.mem_cap_in_bytes_p(mem_cap_in_bytes_p)
   ,.mem_load_p(preload_mem_p)
   ,.mem_zero_p(mem_zero_p)
   ,.mem_file_p(mem_file_p)
   ,.mem_offset_p(mem_offset_p)
 
   ,.use_max_latency_p(use_max_latency_p)
   ,.use_random_latency_p(use_random_latency_p)
   ,.use_dramsim2_latency_p(use_dramsim2_latency_p)
   ,.max_latency_p(max_latency_p)
 
   ,.dram_clock_period_in_ps_p(dram_clock_period_in_ps_p)
   ,.dram_cfg_p(dram_cfg_p)
   ,.dram_sys_cfg_p(dram_sys_cfg_p)
   ,.dram_capacity_p(dram_capacity_p)
   )
 mem
  (.clk_i(clk_i)
   ,.reset_i(reset_i)
 
   ,.mem_cmd_i(proc_mem_cmd_lo)
   ,.mem_cmd_v_i(proc_mem_cmd_ready_li & proc_mem_cmd_v_lo)
   ,.mem_cmd_ready_o(proc_mem_cmd_ready_li)
 
   ,.mem_resp_o(proc_mem_resp_li)
   ,.mem_resp_v_o(proc_mem_resp_v_li)
   ,.mem_resp_yumi_i(proc_mem_resp_yumi_lo)
   );

assign proc_mem_init_done_lo = 1'b1;

  end

logic nbf_done_lo, cfg_done_lo, dram_sel_lo;
if (load_nbf_p)
  begin : nbf
    bp_nonsynth_nbf_loader
     #(.bp_params_p(bp_params_p)
      ,.skip_freeze_clear_p(preload_mem_p))
     nbf_loader
      (.clk_i(clk_i)
       ,.reset_i(reset_i | ~proc_mem_init_done_lo | (preload_mem_p==0 & ~cfg_done_lo))
    
       ,.lce_id_i(lce_id_width_p'('b10))
    
       ,.io_cmd_o(nbf_proc_mem_cmd_lo)
       ,.io_cmd_v_o(nbf_proc_mem_cmd_v_lo)
       ,.io_cmd_yumi_i(nbf_proc_mem_cmd_yumi_li)
    
       ,.io_resp_i(nbf_proc_mem_resp_li)
       ,.io_resp_v_i(nbf_proc_mem_resp_v_li)
       ,.io_resp_ready_o(nbf_proc_mem_resp_ready_lo)
    
       ,.done_o(nbf_done_lo)
       );
    
    if (preload_mem_p)
      begin: bypass
        logic [31:0] counter_r;
        logic nbf_done_r, ref_cycle_lo, ref_cycle_lo_r;
        
        bsg_sync_sync #(.width_p(1)) ref_cycle_bss
        (.oclk_i      ( clk_i   )
        ,.iclk_data_i ( dmc_refresh_lo )
        ,.oclk_data_o ( ref_cycle_lo ));
        
        bsg_dff #(.width_p(1)) ref_cycle_dff
        (.clk_i  (clk_i)
        ,.data_i (ref_cycle_lo)
        ,.data_o (ref_cycle_lo_r)
        );
        
        always_ff @(posedge clk_i)
          begin
            if (reset_i)
              begin
                counter_r <= 0;
                nbf_done_r <= 0;
              end
            else if (nbf_done_lo)
              begin
                if (counter_r == 2)
                  begin
                    nbf_done_r <= 1;
                  end
                else
                  begin
                    counter_r <= counter_r + (ref_cycle_lo & ~ref_cycle_lo_r);
                  end
              end
          end
           
        bp_nbf_to_cce_mem
       #(.bp_params_p(bp_params_p)
        ) nbf_adapter
        (.clk_i(clk_i)
        ,.reset_i(reset_i)

        ,.io_cmd_i(nbf_proc_mem_cmd_lo)
        ,.io_cmd_v_i(nbf_proc_mem_cmd_v_lo)
        ,.io_cmd_yumi_o(nbf_proc_mem_cmd_yumi_li)

        ,.io_resp_o(nbf_proc_mem_resp_li)
        ,.io_resp_v_o(nbf_proc_mem_resp_v_li)
        ,.io_resp_ready_i(nbf_proc_mem_resp_ready_lo)

        ,.mem_cmd_o(a_proc_mem_cmd_lo)
        ,.mem_cmd_v_o(a_proc_mem_cmd_v_lo)
        ,.mem_cmd_yumi_i(a_proc_mem_cmd_yumi_li)

        ,.mem_resp_i(a_proc_mem_resp_li)
        ,.mem_resp_v_i(a_proc_mem_resp_v_li)
        ,.mem_resp_ready_o(a_proc_mem_resp_ready_lo)
        );
        
        assign dram_sel_lo = nbf_done_r;
        
        assign nbf_cmd_lo = '0;
        assign nbf_cmd_v_lo = '0;
        assign nbf_resp_ready_lo = 1'b1;
      end
    else
      begin: direct
        assign dram_sel_lo = 1'b1;
        
        assign nbf_cmd_lo = nbf_proc_mem_cmd_lo;
        assign nbf_cmd_v_lo = nbf_proc_mem_cmd_v_lo;
        assign nbf_proc_mem_cmd_yumi_li = nbf_cmd_yumi_li;
        
        assign nbf_proc_mem_resp_li = nbf_resp_li;
        assign nbf_proc_mem_resp_v_li = nbf_resp_v_li;
        assign nbf_resp_ready_lo = nbf_proc_mem_resp_ready_lo;
      end
    
  end
else
  begin : no_nbf
    assign dram_sel_lo = 1'b1;
    
    assign nbf_resp_ready_lo = 1'b1;
    assign nbf_cmd_v_lo = '0;
    assign nbf_cmd_lo = '0;

    assign nbf_done_lo = 1'b1;
  end


always_comb
  begin
    if (dram_sel_lo)
      begin
        proc_mem_cmd_lo = b_proc_mem_cmd_lo;
        proc_mem_cmd_v_lo = b_proc_mem_cmd_v_lo;
        b_proc_mem_cmd_ready_li = proc_mem_cmd_ready_li;
        
        b_proc_mem_resp_li = proc_mem_resp_li;
        b_proc_mem_resp_v_li = proc_mem_resp_v_li;
        proc_mem_resp_yumi_lo = b_proc_mem_resp_yumi_lo;
        
        a_proc_mem_cmd_yumi_li = a_proc_mem_cmd_v_lo;
        a_proc_mem_resp_li = '0;
        a_proc_mem_resp_v_li = 1'b0;
      end
    else
      begin
        proc_mem_cmd_lo = a_proc_mem_cmd_lo;
        proc_mem_cmd_v_lo = a_proc_mem_cmd_v_lo;
        a_proc_mem_cmd_yumi_li = proc_mem_cmd_v_lo & proc_mem_cmd_ready_li;
        
        a_proc_mem_resp_li = proc_mem_resp_li;
        a_proc_mem_resp_v_li = proc_mem_resp_v_li;
        proc_mem_resp_yumi_lo = a_proc_mem_resp_v_li & a_proc_mem_resp_ready_lo;
        
        b_proc_mem_cmd_ready_li = 1'b1;
        b_proc_mem_resp_li = '0;
        b_proc_mem_resp_v_li = 1'b0;
      end
  end


localparam cce_instr_ram_addr_width_lp = `BSG_SAFE_CLOG2(num_cce_instr_ram_els_p);
bp_cce_mmio_cfg_loader
  #(.bp_params_p(bp_params_p)
    ,.inst_width_p($bits(bp_cce_inst_s))
    ,.inst_ram_addr_width_p(cce_instr_ram_addr_width_lp)
    ,.inst_ram_els_p(num_cce_instr_ram_els_p)
    ,.skip_ram_init_p(skip_init_p)
    ,.clear_freeze_p(!(load_nbf_p == 1 && preload_mem_p == 0))
    )
  cfg_loader
  (.clk_i(clk_i)
   ,.reset_i(reset_i | ~proc_mem_init_done_lo | (~dram_sel_lo))

   ,.lce_id_i(lce_id_width_p'('b10))
    
   ,.io_cmd_o(cfg_cmd_lo)
   ,.io_cmd_v_o(cfg_cmd_v_lo)
   ,.io_cmd_yumi_i(cfg_cmd_yumi_li)

   ,.io_resp_i(cfg_resp_li)
   ,.io_resp_v_i(cfg_resp_v_li)
   ,.io_resp_ready_o(cfg_resp_ready_lo)

   ,.done_o(cfg_done_lo)
  );
  
  logic [31:0] exec_cycle_r;
  bsg_counter_clear_up 
 #(.max_val_p (64'(1<<32-1))
  ,.init_val_p(0)
  ) exec_cycle
  (.clk_i     (clk_i)
  ,.reset_i   (reset_i)
  ,.clear_i   (~cfg_done_lo)
  ,.up_i      (1'b1)
  ,.count_o   (exec_cycle_r)
  );
  

// CFG and NBF are mutex, so we can just use fixed arbitration here
always_comb
  if (~cfg_done_lo)
    begin
      load_cmd_lo = cfg_cmd_lo;
      load_cmd_v_lo = cfg_cmd_v_lo;

      nbf_cmd_yumi_li = '0; 
      cfg_cmd_yumi_li = load_cmd_yumi_li;

      load_resp_ready_lo = cfg_resp_ready_lo;

      nbf_resp_li = '0;
      nbf_resp_v_li = '0;

      cfg_resp_li = load_resp_li;
      cfg_resp_v_li = load_resp_v_li;
    end
  else
    begin
      load_cmd_lo = nbf_cmd_lo;
      load_cmd_v_lo = nbf_cmd_v_lo;

      nbf_cmd_yumi_li = load_cmd_yumi_li; 
      cfg_cmd_yumi_li = '0;

      load_resp_ready_lo = nbf_resp_ready_lo;

      nbf_resp_li = load_resp_li;
      nbf_resp_v_li = load_resp_v_li;

      cfg_resp_li = '0;
      cfg_resp_v_li = '0;
    end

bp_nonsynth_host
 #(.bp_params_p(bp_params_p))
 host
  (.clk_i(clk_i)
   ,.reset_i(reset_i)

   ,.io_cmd_i(proc_io_cmd_lo)
   ,.io_cmd_v_i(proc_io_cmd_v_lo & proc_io_cmd_ready_li)
   ,.io_cmd_ready_o(proc_io_cmd_ready_li)

   ,.io_resp_o(proc_io_resp_li)
   ,.io_resp_v_o(proc_io_resp_v_li)
   ,.io_resp_yumi_i(proc_io_resp_yumi_lo)

   ,.program_finish_o(program_finish_lo)
   );

bind bp_be_top
  bp_nonsynth_commit_tracer
   #(.bp_params_p(bp_params_p))
   commit_tracer
    (.clk_i(clk_i & (testbench.cmt_trace_p == 1))
     ,.reset_i(reset_i)
     ,.freeze_i(be_checker.scheduler.int_regfile.cfg_bus.freeze)

     ,.mhartid_i('0)

     ,.decode_i(be_calculator.reservation_n.decode)

     ,.commit_v_i(be_calculator.commit_pkt.instret)
     ,.commit_pc_i(be_calculator.commit_pkt.pc)
     ,.commit_instr_i(be_calculator.commit_pkt.instr)

     ,.rd_w_v_i(be_checker.scheduler.wb_pkt.rd_w_v)
     ,.rd_addr_i(be_checker.scheduler.wb_pkt.rd_addr)
     ,.rd_data_i(be_checker.scheduler.wb_pkt.rd_data)
     );

  if (num_core_p == 1)
    begin : cosim
      bind bp_be_top
        bp_nonsynth_cosim
         #(.bp_params_p(bp_params_p))
          cosim
          (.clk_i(clk_i)
           ,.reset_i(reset_i)
           ,.freeze_i(be_checker.scheduler.int_regfile.cfg_bus.freeze)
           ,.en_i(testbench.cosim_p == 1)
           ,.cosim_instr_i(testbench.cosim_instr_p)

           ,.mhartid_i(be_checker.scheduler.int_regfile.cfg_bus.core_id)
           // Want to pass config file as a parameter, but cannot in Verilator 4.025
           // Parameter-resolved constants must not use dotted references
           ,.config_file_i(testbench.cosim_cfg_file_p)

           ,.decode_i(be_calculator.reservation_n.decode)

           ,.commit_v_i(be_calculator.commit_pkt.instret)
           ,.commit_pc_i(be_calculator.commit_pkt.pc)
           ,.commit_instr_i(be_calculator.commit_pkt.instr)

           ,.rd_w_v_i(be_checker.scheduler.wb_pkt.rd_w_v)
           ,.rd_addr_i(be_checker.scheduler.wb_pkt.rd_addr)
           ,.rd_data_i(be_checker.scheduler.wb_pkt.rd_data)

           ,.interrupt_v_i(be_mem.csr.trap_pkt_cast_o._interrupt)
           ,.cause_i(be_mem.csr.trap_pkt_cast_o.cause)

           ,.finish_o(testbench.cosim_finish_lo)
           );
    end
  else
    begin : no_cosim
      assign cosim_finish_lo = '0;
    end

bind bp_be_top
  bp_be_nonsynth_perf
   #(.bp_params_p(bp_params_p))
   perf
    (.clk_i(clk_i)
     ,.reset_i(reset_i)
     ,.freeze_i(be_checker.scheduler.int_regfile.cfg_bus.freeze)
     ,.warmup_instr_i(testbench.warmup_instr_p)

     ,.mhartid_i(be_checker.scheduler.int_regfile.cfg_bus.core_id)

     ,.commit_v_i(be_calculator.commit_pkt.instret)

     ,.program_finish_i(testbench.program_finish_lo | testbench.cosim_finish_lo)
     );

  bind bp_be_top
    bp_nonsynth_watchdog
     #(.bp_params_p(bp_params_p)
       ,.timeout_cycles_p(100000)
       ,.heartbeat_instr_p(100000)
       )
     watchdog
      (.clk_i(clk_i)
       ,.reset_i(reset_i)
       ,.freeze_i(be_checker.scheduler.int_regfile.cfg_bus.freeze)

       ,.mhartid_i(be_checker.scheduler.int_regfile.cfg_bus.core_id)

       ,.npc_i(be_checker.director.npc_r)
       ,.instret_i(be_calculator.commit_pkt.instret)
       );

  bind bp_be_director
    bp_be_nonsynth_npc_tracer
     #(.bp_params_p(bp_params_p))
     npc_tracer
      (.clk_i(clk_i & (testbench.npc_trace_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(be_checker.scheduler.int_regfile.cfg_bus.freeze)

       ,.mhartid_i(be_checker.scheduler.int_regfile.cfg_bus.core_id)

       ,.npc_w_v(npc_w_v)
       ,.npc_n(npc_n)
       ,.npc_r(npc_r)
       ,.expected_npc_o(expected_npc_o)

       ,.fe_cmd_i(fe_cmd)
       ,.fe_cmd_v(fe_cmd_v)

       ,.commit_pkt_i(commit_pkt)
       );

  bind bp_be_dcache
    bp_nonsynth_cache_tracer
     #(.bp_params_p(bp_params_p)
      ,.assoc_p(dcache_assoc_p)
      ,.sets_p(dcache_sets_p)
      ,.block_width_p(dcache_block_width_p)
      ,.trace_file_p("dcache"))
     dcache_tracer
      (.clk_i(clk_i & (testbench.dcache_trace_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(cfg_bus_cast_i.freeze)

       ,.mhartid_i(cfg_bus_cast_i.core_id)

       ,.v_tl_r(v_tl_r)
       
       ,.v_tv_r(v_tv_r)
       ,.addr_tv_r(paddr_tv_r)
       ,.lr_miss_tv(lr_miss_tv)
       ,.sc_op_tv_r(sc_op_tv_r)
       ,.sc_success(sc_success)
        
       ,.cache_req_v_o(cache_req_v_o)
       ,.cache_req_o(cache_req_o)

       ,.cache_req_metadata_o(cache_req_metadata_o)
       ,.cache_req_metadata_v_o(cache_req_metadata_v_o)
        
       ,.cache_req_complete_i(cache_req_complete_i)

       ,.v_o(v_o)
       ,.load_data(data_o)
       ,.cache_miss_o(dcache_miss_o)
       ,.wt_req(wt_req)
       ,.store_data(data_tv_r)

       ,.data_mem_pkt_v_i(data_mem_pkt_v_i)
       ,.data_mem_pkt_i(data_mem_pkt_i)
       ,.data_mem_pkt_yumi_o(data_mem_pkt_yumi_o)
       
       ,.tag_mem_pkt_v_i(tag_mem_pkt_v_i)
       ,.tag_mem_pkt_i(tag_mem_pkt_i)
       ,.tag_mem_pkt_yumi_o(tag_mem_pkt_yumi_o)

       ,.stat_mem_pkt_v_i(stat_mem_pkt_v_i)
       ,.stat_mem_pkt_i(stat_mem_pkt_i)
       ,.stat_mem_pkt_yumi_o(stat_mem_pkt_yumi_o)
       );

  bind bp_fe_icache
    bp_nonsynth_cache_tracer
     #(.bp_params_p(bp_params_p)
      ,.assoc_p(icache_assoc_p)
      ,.sets_p(icache_sets_p)
      ,.block_width_p(icache_block_width_p)
      ,.trace_file_p("icache"))
     icache_tracer
      (.clk_i(clk_i & (testbench.icache_trace_p == 1))
       ,.reset_i(reset_i)
       
       ,.freeze_i(cfg_bus_cast_i.freeze)
       ,.mhartid_i(cfg_bus_cast_i.core_id)

       ,.v_tl_r(v_tl_r)
       
       ,.v_tv_r(v_tv_r)
       ,.addr_tv_r(addr_tv_r)
       ,.lr_miss_tv(1'b0)
       ,.sc_op_tv_r(1'b0)
       ,.sc_success(1'b0)
        
       ,.cache_req_v_o(cache_req_v_o)
       ,.cache_req_o(cache_req_o)

       ,.cache_req_metadata_o(cache_req_metadata_o)
       ,.cache_req_metadata_v_o(cache_req_metadata_v_o)
        
       ,.cache_req_complete_i(cache_req_complete_i)

       ,.v_o(data_v_o)
       ,.load_data(dword_width_p'(data_o))
       ,.cache_miss_o(miss_o)
       ,.wt_req()
       ,.store_data(dword_width_p'(0))

       ,.data_mem_pkt_v_i(data_mem_pkt_v_i)
       ,.data_mem_pkt_i(data_mem_pkt_i)
       ,.data_mem_pkt_yumi_o(data_mem_pkt_yumi_o)
       
       ,.tag_mem_pkt_v_i(tag_mem_pkt_v_i)
       ,.tag_mem_pkt_i(tag_mem_pkt_i)
       ,.tag_mem_pkt_yumi_o(tag_mem_pkt_yumi_o)

       ,.stat_mem_pkt_v_i(stat_mem_pkt_v_i)
       ,.stat_mem_pkt_i(stat_mem_pkt_i)
       ,.stat_mem_pkt_yumi_o(stat_mem_pkt_yumi_o)
       );

  bind bp_core_minimal
    bp_be_nonsynth_vm_tracer
    #(.bp_params_p(bp_params_p))
    vm_tracer
      (.clk_i(clk_i & (testbench.vm_trace_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(be.be_checker.scheduler.int_regfile.cfg_bus.freeze)

       ,.mhartid_i(be.be_checker.scheduler.int_regfile.cfg_bus.core_id)

       ,.itlb_clear_i(fe.mem.itlb.flush_i)
       ,.itlb_fill_v_i(fe.mem.itlb.v_i & fe.mem.itlb.w_i)
       ,.itlb_vtag_i(fe.mem.itlb.vtag_i)
       ,.itlb_entry_i(fe.mem.itlb.entry_i)

       ,.dtlb_clear_i(be.be_mem.dtlb.flush_i)
       ,.dtlb_fill_v_i(be.be_mem.dtlb.v_i & be.be_mem.dtlb.w_i)
       ,.dtlb_vtag_i(be.be_mem.dtlb.vtag_i)
       ,.dtlb_entry_i(be.be_mem.dtlb.entry_i)
       );

  bp_mem_nonsynth_tracer
   #(.bp_params_p(bp_params_p))
   bp_mem_tracer
    (.clk_i(clk_i & (testbench.dram_trace_p == 1))
     ,.reset_i(reset_i)

     ,.mem_cmd_i(proc_mem_cmd_lo)
     ,.mem_cmd_v_i(proc_mem_cmd_v_lo & proc_mem_cmd_ready_li)
     ,.mem_cmd_ready_i(proc_mem_cmd_ready_li)

     ,.mem_resp_i(proc_mem_resp_li)
     ,.mem_resp_v_i(proc_mem_resp_v_li)
     ,.mem_resp_yumi_i(proc_mem_resp_yumi_lo)
     );

  bind bp_core_minimal
    bp_nonsynth_core_profiler
     #(.bp_params_p(bp_params_p))
     core_profiler
      (.clk_i(clk_i & (testbench.core_profile_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(be.be_checker.scheduler.int_regfile.cfg_bus.freeze)

       ,.mhartid_i(be.be_checker.scheduler.int_regfile.cfg_bus.core_id)

       ,.fe_wait_stall(fe.pc_gen.is_wait)
       ,.fe_queue_stall(~fe.pc_gen.fe_queue_ready_i)

       ,.itlb_miss(fe.mem.itlb_miss_r)
       ,.icache_miss(~fe.mem.icache.vaddr_ready_o | fe.pc_gen.icache_miss)
       ,.icache_fence(fe.mem.icache.fencei_req)
       ,.branch_override(fe.pc_gen.ovr_taken & ~fe.pc_gen.ovr_ret)
       ,.ret_override(fe.pc_gen.ovr_ret)

       ,.fe_cmd(fe.pc_gen.fe_cmd_yumi_o & ~fe.pc_gen.attaboy_v)

       ,.mispredict(be.be_checker.director.npc_mismatch_v)
       ,.target(be.be_checker.director.isd_status.isd_pc)

       ,.dtlb_miss(be.be_mem.dtlb_miss_r)
       ,.dcache_miss(~be.be_mem.dcache.ready_o)
       ,.long_haz(be.be_checker.detector.long_haz_v)
       ,.exception(be.be_checker.director.trap_pkt.exception)
       ,.eret(be.be_checker.director.trap_pkt.eret)
       ,._interrupt(be.be_checker.director.trap_pkt._interrupt)
       ,.control_haz(be.be_checker.detector.control_haz_v)
       ,.data_haz(be.be_checker.detector.data_haz_v)
       ,.load_dep((be.be_checker.detector.dep_status_li[0].mem_iwb_v
                   | be.be_checker.detector.dep_status_li[1].mem_iwb_v
                   ) & be.be_checker.detector.data_haz_v
                  )
       ,.mul_dep((be.be_checker.detector.dep_status_li[0].mul_iwb_v
                  | be.be_checker.detector.dep_status_li[1].mul_iwb_v
                  | be.be_checker.detector.dep_status_li[2].mul_iwb_v
                  ) & be.be_checker.detector.data_haz_v
                 )
       ,.struct_haz(be.be_checker.detector.struct_haz_v)

       ,.reservation(be.be_calculator.reservation_n)
       ,.commit_pkt(be.be_calculator.commit_pkt)
       ,.trap_pkt(be.be_mem.csr.trap_pkt_o)
       );

  bind bp_core_minimal
    bp_nonsynth_pc_profiler
     #(.bp_params_p(bp_params_p))
     pc_profiler
      (.clk_i(clk_i & (testbench.core_profile_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(be.be_checker.scheduler.int_regfile.cfg_bus.freeze)

       ,.mhartid_i(be.be_checker.scheduler.int_regfile.cfg_bus.core_id)

       ,.commit_pkt(be.be_calculator.commit_pkt)

       ,.program_finish_i(testbench.program_finish_lo | testbench.cosim_finish_lo)
       );

  bind bp_be_director
    bp_nonsynth_branch_profiler
     #(.bp_params_p(bp_params_p))
     pc_profiler
      (.clk_i(clk_i & (testbench.core_profile_p == 1))
       ,.reset_i(reset_i)
       ,.freeze_i(cfg_bus_cast_i.freeze)

       ,.mhartid_i(cfg_bus_cast_i.core_id)

       ,.fe_cmd_o(fe_cmd_o)
       ,.fe_cmd_v_o(fe_cmd_v_o)
       ,.fe_cmd_ready_i(fe_cmd_ready_i)

       ,.commit_v_i(commit_pkt.instret)

       ,.program_finish_i(testbench.program_finish_lo | testbench.cosim_finish_lo)
       );

  if (cce_trace_p) begin : cce_tracer
  bind bp_cce_wrapper
    bp_me_nonsynth_cce_tracer
     #(.bp_params_p(bp_params_p))
     cce_tracer
      (.clk_i(clk_i & (testbench.cce_trace_p == 1))
      ,.reset_i(reset_i)
      ,.freeze_i(cfg_bus_cast_i.freeze)

      ,.cce_id_i(cfg_bus_cast_i.cce_id)

      // To CCE
      ,.lce_req_i(lce_req_i)
      ,.lce_req_v_i(lce_req_v_i)
      ,.lce_req_yumi_i(lce_req_yumi_o)
      ,.lce_resp_i(lce_resp_i)
      ,.lce_resp_v_i(lce_resp_v_i)
      ,.lce_resp_yumi_i(lce_resp_yumi_o)

      // From CCE
      ,.lce_cmd_i(lce_cmd_o)
      ,.lce_cmd_v_i(lce_cmd_v_o)
      ,.lce_cmd_ready_i(lce_cmd_ready_i)

      // To CCE
      ,.mem_resp_i(mem_resp_i)
      ,.mem_resp_v_i(mem_resp_v_i)
      ,.mem_resp_yumi_i(mem_resp_yumi_o)

      // From CCE
      ,.mem_cmd_i(mem_cmd_o)
      ,.mem_cmd_v_i(mem_cmd_v_o)
      ,.mem_cmd_ready_i(mem_cmd_ready_i)
      );
  end


bp_nonsynth_if_verif
 #(.bp_params_p(bp_params_p))
 if_verif
  ();

endmodule

