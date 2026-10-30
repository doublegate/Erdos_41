//! ============================================================================
//! `gpu.rs` — CUDA driver context and runtime NVRTC compilation for `erdos41`.
//! ============================================================================
//!
//! Uses `cudarc` with `dynamic-loading`, so `libcuda.so` and `libnvrtc.so` are
//! loaded via `dlopen` only when a GPU path is invoked. CPU-only commands and
//! the default CI test suite run on hosts without an Nvidia GPU.

use anyhow::{Context, Result};
use cudarc::driver::{CudaContext, CudaFunction, CudaModule, CudaStream, LaunchConfig};
use cudarc::nvrtc::{compile_ptx_with_opts, CompileOptions};
use std::sync::Arc;

pub const KERNEL_SRC: &str = include_str!("kernels.cu");

pub struct Gpu {
    pub ctx: Arc<CudaContext>,
    pub stream: Arc<CudaStream>,
    pub module: Arc<CudaModule>,
    pub fn_dfs_b3_ruler: CudaFunction,
    pub fn_eval_b3_conservation: CudaFunction,
    pub fn_eval_b3_sign_cones: CudaFunction,
    pub fn_eval_b3_full_cube: CudaFunction,
    pub fn_eval_sublevel_subcone_weights: CudaFunction,
    pub fn_eval_bp_projective_fermat: CudaFunction,
    pub fn_eval_three_hemisphere_cone: CudaFunction,
    pub fn_eval_telescoping_third_hemisphere: CudaFunction,
    pub fn_eval_horizon_truncated_rays: CudaFunction,
    pub fn_eval_quadratic_injection_rays: CudaFunction,
    pub fn_eval_b3_diophantine_haar_closure: CudaFunction,
    pub device_name: String,
    pub sm_count: i32,
}

impl Gpu {
    pub fn init(device_ordinal: usize, arch: &str) -> Result<Self> {
        let ctx = CudaContext::new(device_ordinal)
            .with_context(|| format!("failed to initialize CUDA device {device_ordinal}"))?;
        let stream = ctx.default_stream();
        let device_name = ctx
            .name()
            .unwrap_or_else(|_| "Unknown CUDA GPU".to_string());
        let sm_count = ctx
            .attribute(
                cudarc::driver::sys::CUdevice_attribute::CU_DEVICE_ATTRIBUTE_MULTIPROCESSOR_COUNT,
            )
            .unwrap_or(82);

        let arch_flag = format!("--gpu-architecture={arch}");
        let opts = CompileOptions {
            options: vec![arch_flag, "--use_fast_math".to_string()],
            ..Default::default()
        };
        let ptx = compile_ptx_with_opts(KERNEL_SRC, opts)
            .context("NVRTC compilation of src/kernels.cu failed")?;
        let module = ctx
            .load_module(ptx)
            .context("failed to load compiled PTX module")?;

        let fn_dfs_b3_ruler = module
            .load_function("k_dfs_b3_ruler")
            .context("missing kernel k_dfs_b3_ruler")?;
        let fn_eval_b3_conservation = module
            .load_function("k_eval_b3_conservation")
            .context("missing kernel k_eval_b3_conservation")?;
        let fn_eval_b3_sign_cones = module
            .load_function("k_eval_b3_sign_cones")
            .context("missing kernel k_eval_b3_sign_cones")?;
        let fn_eval_b3_full_cube = module
            .load_function("k_eval_b3_full_cube")
            .context("missing kernel k_eval_b3_full_cube")?;
        let fn_eval_sublevel_subcone_weights = module
            .load_function("k_eval_sublevel_subcone_weights")
            .context("missing kernel k_eval_sublevel_subcone_weights")?;
        let fn_eval_bp_projective_fermat = module
            .load_function("k_eval_bp_projective_fermat")
            .context("missing kernel k_eval_bp_projective_fermat")?;
        let fn_eval_three_hemisphere_cone = module
            .load_function("k_eval_three_hemisphere_cone")
            .context("missing kernel k_eval_three_hemisphere_cone")?;
        let fn_eval_telescoping_third_hemisphere = module
            .load_function("k_eval_telescoping_third_hemisphere")
            .context("missing kernel k_eval_telescoping_third_hemisphere")?;
        let fn_eval_horizon_truncated_rays = module
            .load_function("k_eval_horizon_truncated_rays")
            .context("missing kernel k_eval_horizon_truncated_rays")?;
        let fn_eval_quadratic_injection_rays = module
            .load_function("k_eval_quadratic_injection_rays")
            .context("missing kernel k_eval_quadratic_injection_rays")?;
        let fn_eval_b3_diophantine_haar_closure = module
            .load_function("k_eval_b3_diophantine_haar_closure")
            .context("missing kernel k_eval_b3_diophantine_haar_closure")?;

        Ok(Self {
            ctx,
            stream,
            module,
            fn_dfs_b3_ruler,
            fn_eval_b3_conservation,
            fn_eval_b3_sign_cones,
            fn_eval_b3_full_cube,
            fn_eval_sublevel_subcone_weights,
            fn_eval_bp_projective_fermat,
            fn_eval_three_hemisphere_cone,
            fn_eval_telescoping_third_hemisphere,
            fn_eval_horizon_truncated_rays,
            fn_eval_quadratic_injection_rays,
            fn_eval_b3_diophantine_haar_closure,
            device_name,
            sm_count,
        })
    }

    pub fn launch_cfg(&self, n_items: u32) -> LaunchConfig {
        let block_dim = 128u32;
        let grid_dim = n_items.div_ceil(block_dim).max(1);
        LaunchConfig {
            grid_dim: (grid_dim, 1, 1),
            block_dim: (block_dim, 1, 1),
            shared_mem_bytes: 0,
        }
    }
}
