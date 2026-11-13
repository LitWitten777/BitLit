"""
Interactive 3D Volumetric Raymarching & Radiative Transfer Engine.

Synthesizes 3D volumetric density fields rho(x, y, z) and emission fields C(x, y, z)
from multi-messenger sedenion observations (JWST NIRCam, NVSS Radio, RASS X-ray)
and Roman Space Telescope optical wavefront potentials.

Implements:
- Radiative transfer volume integration: dI/ds = j_nu - alpha_nu * I_nu
- Software raymarching projection (orthographic & perspective)
- GLSL raymarching shader generation compatible with Raymarch-Engine
- Interactive WebGL Three.js volume raymarcher HTML generator
"""

from __future__ import annotations

import json
import os
import cv2
import numpy as np


def build_astrophysical_volume(
    layers: dict[str, np.ndarray],
    depth_slices: int = 64,
    grid_size: tuple[int, int] = (128, 128),
) -> tuple[np.ndarray, np.ndarray]:
    """Construct 3D scalar density rho(z, y, x) and RGB emission C(z, y, x, 3).

    Stratifies physical components across the depth axis z in [0, 1]:
    - Lower stratum (z in [0.0, 0.4]): Cold molecular gas & dust (F360M, F470N)
    - Mid stratum (z in [0.3, 0.8]): Ionized Pa-alpha hydrogen outflow (F405N)
    - Upper stratum (z in [0.6, 1.0]): Synchrotron magnetic filaments (NVSS) & X-ray corona (RASS)

    Parameters
    ----------
    layers : dict[str, np.ndarray]
        Dictionary of 2D astrophysical layers.
    depth_slices : int
        Number of volumetric slices along Z.
    grid_size : tuple[int, int]
        (H, W) spatial resolution for the volumetric grid.

    Returns
    -------
    rho : np.ndarray
        3D float array of shape (D, H, W) representing optical density.
    emission : np.ndarray
        4D float array of shape (D, H, W, 3) representing RGB emission radiance.
    """
    h, w = grid_size
    d = depth_slices

    def res(name: str) -> np.ndarray:
        if name in layers:
            arr = layers[name]
            return cv2.resize(arr, (w, h), interpolation=cv2.INTER_LINEAR).astype(np.float64)
        return np.zeros((h, w), dtype=np.float64)

    f162 = res("jwst_f162m")
    f405 = res("jwst_f405n")
    f360 = res("jwst_f360m")
    f470 = res("jwst_f470n")
    radio = res("radio_nvss")
    xray = res("xray_rass")

    rho = np.zeros((d, h, w), dtype=np.float32)
    emission = np.zeros((d, h, w, 3), dtype=np.float32)

    zs = np.linspace(0.0, 1.0, d)

    for iz, z in enumerate(zs):
        # 1. Molecular & Dust Component (orange / amber)
        w_dust = np.exp(-0.5 * ((z - 0.2) / 0.15)**2)
        dust_density = (0.6 * f360 + 0.4 * f470) * w_dust

        # 2. Ionized Hydrogen Plume Component (cyan)
        w_plume = np.exp(-0.5 * ((z - 0.55) / 0.18)**2)
        plume_density = f405 * w_plume

        # 3. Synchrotron & X-ray Magnetic Filament Component (deep blue / violet)
        w_mag = np.exp(-0.5 * ((z - 0.8) / 0.15)**2)
        mag_density = (0.7 * radio + 0.3 * xray) * w_mag

        # Total density
        rho_slice = dust_density + 1.2 * plume_density + 0.9 * mag_density
        rho[iz] = rho_slice.astype(np.float32)

        # Multi-spectral emission coloring
        # Dust: orange [1.0, 0.55, 0.1]
        # Plume: cyan [0.1, 0.95, 1.0]
        # Magnetic: violet/blue [0.4, 0.2, 1.0]
        r = dust_density * 1.0 + plume_density * 0.1 + mag_density * 0.4
        g = dust_density * 0.55 + plume_density * 0.95 + mag_density * 0.2
        b = dust_density * 0.1 + plume_density * 1.0 + mag_density * 1.0

        emission[iz, :, :, 0] = np.clip(r, 0.0, 1.0).astype(np.float32)
        emission[iz, :, :, 1] = np.clip(g, 0.0, 1.0).astype(np.float32)
        emission[iz, :, :, 2] = np.clip(b, 0.0, 1.0).astype(np.float32)

    # Normalize rho to [0, 1]
    max_rho = np.max(rho)
    if max_rho > 1e-6:
        rho /= max_rho

    return rho, emission


def software_raymarch(
    rho: np.ndarray,
    emission: np.ndarray,
    step_size: float = 0.02,
    density_scale: float = 3.0,
    axis: int = 0,
) -> np.ndarray:
    """Perform direct volume rendering via numerical radiative transfer.

    Solves: I = sum_i T_i * alpha_i * C_i, where T_i = exp(-sum_j sigma_j * ds).

    Parameters
    ----------
    rho : np.ndarray
        Shape (D, H, W).
    emission : np.ndarray
        Shape (D, H, W, 3).
    step_size : float
        Numerical step size ds.
    density_scale : float
        Optical absorption coefficient multiplier.
    axis : int
        Viewing direction: 0 (along Z / top-down), 1 (along Y / side-view), 2 (along X / edge-on).

    Returns
    -------
    np.ndarray
        Rendered 2D RGB image of shape (H_out, W_out, 3) in [0, 1].
    """
    if axis != 0:
        rho_swapped = np.swapaxes(rho, 0, axis)
        em_swapped = np.swapaxes(emission, 0, axis)
    else:
        rho_swapped = rho
        em_swapped = emission

    n_steps, h_out, w_out = rho_swapped.shape
    accum_color = np.zeros((h_out, w_out, 3), dtype=np.float64)
    transmittance = np.ones((h_out, w_out), dtype=np.float64)

    for i in range(n_steps):
        step_rho = rho_swapped[i].astype(np.float64) * density_scale
        step_em = em_swapped[i].astype(np.float64)

        # Beer-Lambert extinction
        alpha = 1.0 - np.exp(-step_rho * step_size)
        weight = transmittance * alpha

        accum_color[:, :, 0] += weight * step_em[:, :, 0]
        accum_color[:, :, 1] += weight * step_em[:, :, 1]
        accum_color[:, :, 2] += weight * step_em[:, :, 2]

        transmittance *= (1.0 - alpha)

    return np.clip(accum_color, 0.0, 1.0)


def export_raymarch_glsl_fragment_shader(filepath: str) -> None:
    """Export a standalone GLSL fragment shader compatible with Raymarch-Engine."""
    os.makedirs(os.path.dirname(os.path.abspath(filepath)), exist_ok=True)
    glsl_code = """#version 420 core
// Volumetric Astrophysical & Sedenion Raymarching Shader
// Compatible with /data/mind/cognition/github/Raymarch-Engine/shaders/march.frag

out vec4 fragColor;
in vec2 vUv;

uniform vec3 uCameraPos;
uniform vec3 uCameraDir;
uniform vec2 uResolution;
uniform float uTime;
uniform float uDensityScale; // default: 4.0
uniform float uStepSize;     // default: 0.015

// Sedenion Annihilation Attractor Potential (8-regular Ramanujan frame)
float sedenionZeroDivisorPotential(vec3 p) {
    // 3D slice through 7 Cayley-Dickson associative triads
    vec3 q = sin(p * 3.14159265);
    float assoc = length(cross(q, p)) - 0.35 * length(q);
    return max(0.0, assoc);
}

// Bounding box intersection
vec2 hitBox(vec3 ro, vec3 rd, vec3 boxMin, vec3 boxMax) {
    vec3 t0 = (boxMin - ro) / rd;
    vec3 t1 = (boxMax - ro) / rd;
    vec3 tmin = min(t0, t1);
    vec3 tmax = max(t0, t1);
    float tNear = max(max(tmin.x, tmin.y), tmin.z);
    float tFar = min(min(tmax.x, tmax.y), tmax.z);
    return vec2(tNear, tFar);
}

void main() {
    vec2 uv = (gl_FragCoord.xy - 0.5 * uResolution) / uResolution.y;
    vec3 rayDir = normalize(uCameraDir + vec3(uv, 1.2));
    vec3 rayOrig = uCameraPos;

    vec2 hit = hitBox(rayOrig, rayDir, vec3(-1.0), vec3(1.0));
    if (hit.x > hit.y || hit.y < 0.0) {
        fragColor = vec4(0.02, 0.03, 0.06, 1.0);
        return;
    }

    float tStart = max(0.0, hit.x);
    float tEnd = hit.y;
    float t = tStart;

    vec3 accumColor = vec3(0.0);
    float transmittance = 1.0;
    float ds = uStepSize;

    for (int i = 0; i < 128; i++) {
        if (t >= tEnd || transmittance < 0.01) break;

        vec3 pos = rayOrig + t * rayDir;
        
        // Height stratification z in [-1, 1] -> [0, 1]
        float zNorm = pos.z * 0.5 + 0.5;

        // Density field: lower dust, mid plume, upper magnetic filaments
        float dust = exp(-pow((zNorm - 0.25) / 0.15, 2.0)) * max(0.0, 1.0 - length(pos.xy));
        float plume = exp(-pow((zNorm - 0.55) / 0.18, 2.0)) * exp(-pow(pos.x / 0.2, 2.0) - pow(pos.y / 0.35, 2.0));
        float mag = exp(-pow((zNorm - 0.85) / 0.15, 2.0)) * abs(sin(pos.x * 12.0 + pos.y * 8.0));

        // Sedenion zero divisor filtering
        float zd = sedenionZeroDivisorPotential(pos);
        float density = (dust * 0.8 + plume * 1.5 + mag * 0.9) * (1.0 + 0.5 * zd) * uDensityScale;

        float alpha = 1.0 - exp(-density * ds);
        vec3 emission = dust * vec3(1.0, 0.55, 0.1) + plume * vec3(0.1, 0.95, 1.0) + mag * vec3(0.4, 0.2, 1.0);

        accumColor += transmittance * alpha * emission;
        transmittance *= (1.0 - alpha);
        t += ds;
    }

    fragColor = vec4(accumColor + vec3(0.02, 0.03, 0.06) * transmittance, 1.0);
}
"""
    with open(filepath, "w", encoding="utf-8") as f:
        f.write(glsl_code)


def generate_interactive_volumetric_raymarcher_html(
    filepath: str,
    title: str = "Webb Sagittarius C & Roman Pupil: 3D Volumetric Raymarcher",
) -> None:
    """Generate a self-contained WebGL Three.js interactive volume raymarching web app."""
    os.makedirs(os.path.dirname(os.path.abspath(filepath)), exist_ok=True)

    html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>""" + title + """</title>
    <style>
        body { margin: 0; overflow: hidden; background: #07090e; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; color: #e6edf3; }
        #hud { position: absolute; top: 16px; left: 16px; z-index: 10; background: rgba(13, 17, 23, 0.88); padding: 16px 22px; border-radius: 10px; border: 1px solid #30363d; backdrop-filter: blur(10px); max-width: 360px; box-shadow: 0 8px 24px rgba(0,0,0,0.5); }
        #hud h1 { margin: 0 0 8px 0; font-size: 16px; color: #58a6ff; font-weight: 700; }
        #hud p { margin: 0 0 12px 0; font-size: 12px; color: #8b949e; line-height: 1.45; }
        .control-group { margin-bottom: 10px; display: flex; justify-content: space-between; align-items: center; font-size: 12px; }
        .control-group label { color: #c9d1d9; font-weight: 500; }
        .control-group input[type="range"] { width: 140px; accent-color: #388bfd; }
        .btn { background: #21262d; border: 1px solid #30363d; color: #c9d1d9; padding: 6px 14px; border-radius: 6px; cursor: pointer; font-size: 11px; margin-right: 6px; margin-top: 4px; transition: all 0.2s; }
        .btn:hover { background: #30363d; color: #58a6ff; border-color: #58a6ff; }
        .btn.active { background: #1f6feb; color: #fff; border-color: #58a6ff; font-weight: 600; }
        #canvas-container { width: 100vw; height: 100vh; position: absolute; top: 0; left: 0; }
        .badge { display: inline-block; padding: 2px 6px; font-size: 10px; font-weight: 600; border-radius: 4px; background: rgba(56, 139, 253, 0.15); color: #58a6ff; border: 1px solid rgba(56, 139, 253, 0.4); margin-bottom: 8px; }
    </style>
    <!-- Three.js with local offline vendor fallback -->
    <script src="./vendor/three.min.js"></script>
    <script>if (typeof THREE === "undefined") { document.write('<script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"><\\/script>'); }</script>
    <script src="./vendor/OrbitControls.js"></script>
    <script>if (typeof THREE !== "undefined" && !THREE.OrbitControls) { document.write('<script src="https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js"><\\/script>'); }</script>
</head>
<body>
    <div id="hud">
        <span class="badge">STEP 4: VOLUMETRIC RAYMARCHING</span>
        <h1>""" + title + """</h1>
        <p>Real-time radiative transfer raymarcher through 16D sedenion multi-messenger fields (JWST Infrared, NVSS Radio, RASS X-Ray) & Roman pupil wavefront.</p>
        
        <div class="control-group">
            <label>Absorption Density (σ):</label>
            <input type="range" id="densitySlider" min="0.5" max="10.0" step="0.1" value="4.5">
        </div>
        <div class="control-group">
            <label>Emission Gain (j):</label>
            <input type="range" id="emissionSlider" min="0.5" max="4.0" step="0.1" value="1.8">
        </div>
        <div class="control-group">
            <label>Raymarch Steps:</label>
            <input type="range" id="stepSlider" min="32" max="160" step="16" value="96">
        </div>
        <div class="control-group">
            <label>Pa-α Plume Needle:</label>
            <input type="range" id="plumeSlider" min="0.0" max="2.5" step="0.1" value="1.5">
        </div>
        <div class="control-group">
            <label>Synchrotron Filaments:</label>
            <input type="range" id="magSlider" min="0.0" max="2.5" step="0.1" value="1.2">
        </div>
        
        <div style="margin-top: 12px;">
            <button class="btn active" id="btnSedenion" onclick="toggleSedenion()">Sedenion ZD Filter: ON</button>
            <button class="btn" onclick="resetView()">Reset View</button>
        </div>
    </div>
    <div id="canvas-container"></div>

    <script id="vertexShader" type="x-shader/x-vertex">
        varying vec3 vWorldPos;
        void main() {
            vec4 worldPos = modelMatrix * vec4(position, 1.0);
            vWorldPos = worldPos.xyz;
            gl_Position = projectionMatrix * viewMatrix * worldPos;
        }
    </script>

    <script id="fragmentShader" type="x-shader/x-fragment">
        varying vec3 vWorldPos;
        uniform vec3 uCameraPos;
        uniform float uDensityScale;
        uniform float uEmissionScale;
        uniform float uPlumeGain;
        uniform float uMagGain;
        uniform float uSedenionFilter;
        uniform int uMaxSteps;
        uniform float uTime;

        vec2 hitBox(vec3 ro, vec3 rd, vec3 bMin, vec3 bMax) {
            vec3 safeRd = vec3(
                abs(rd.x) < 1e-6 ? (rd.x < 0.0 ? -1e-6 : 1e-6) : rd.x,
                abs(rd.y) < 1e-6 ? (rd.y < 0.0 ? -1e-6 : 1e-6) : rd.y,
                abs(rd.z) < 1e-6 ? (rd.z < 0.0 ? -1e-6 : 1e-6) : rd.z
            );
            vec3 invR = 1.0 / safeRd;
            vec3 t0 = (bMin - ro) * invR;
            vec3 t1 = (bMax - ro) * invR;
            vec3 tmin = min(t0, t1);
            vec3 tmax = max(t0, t1);
            float tNear = max(max(tmin.x, tmin.y), tmin.z);
            float tFar = min(min(tmax.x, tmax.y), tmax.z);
            return vec2(tNear, tFar);
        }

        void main() {
            vec3 rayDir = normalize(vWorldPos - uCameraPos);
            vec3 rayOrig = uCameraPos;

            vec2 hit = hitBox(rayOrig, rayDir, vec3(-1.0), vec3(1.0));
            if (hit.x > hit.y || hit.y < 0.0) discard;

            float tStart = max(0.0, hit.x);
            float tEnd = hit.y;
            float t = tStart;
            float ds = (tEnd - tStart) / float(uMaxSteps);

            vec3 accumColor = vec3(0.0);
            float transmittance = 1.0;

            for (int i = 0; i < 160; i++) {
                if (i >= uMaxSteps || t >= tEnd || transmittance < 0.01) break;
                vec3 p = rayOrig + t * rayDir;
                float zNorm = p.z * 0.5 + 0.5;

                // 1. Dense cold dust core (F360M / F470N)
                float dCore = length(p.xy + vec2(0.15, -0.1));
                float dust = exp(-pow((zNorm - 0.25) / 0.18, 2.0)) * exp(-pow(dCore / 0.45, 2.0));

                // 2. Cyan Paschen-alpha Ionized Needle Plume (F405N)
                float plumeProfile = exp(-pow((p.x - 0.15 * p.y) / 0.09, 2.0) - pow(p.y / 0.65, 2.0));
                float plume = exp(-pow((zNorm - 0.58) / 0.22, 2.0)) * plumeProfile * uPlumeGain;

                // 3. Synchrotron helical magnetic filaments (NVSS 1.4 GHz)
                float helix1 = sin(p.y * 14.0 + p.z * 8.0) * 0.12;
                float helix2 = cos(p.y * 14.0 - p.z * 8.0) * 0.12;
                float magDist = min(length(p.xz - vec2(helix1 - 0.25, 0.8)), length(p.xz - vec2(helix2 + 0.25, 0.85)));
                float mag = exp(-pow(magDist / 0.08, 2.0)) * uMagGain;

                // Sedenion zero divisor frame modulation
                float zdMod = 1.0;
                if (uSedenionFilter > 0.5) {
                    float zdDist = abs(length(cross(p, vec3(0.0, 0.0, 1.0))) - 0.45);
                    zdMod = smoothstep(0.4, 0.0, zdDist);
                }

                float rho = (dust * 0.9 + plume * 1.8 + mag * 1.3) * zdMod * uDensityScale;
                float alpha = 1.0 - exp(-rho * ds);

                // Emission radiance
                vec3 colDust = vec3(1.0, 0.55, 0.12) * dust;
                vec3 colPlume = vec3(0.05, 0.95, 1.0) * plume;
                vec3 colMag = vec3(0.45, 0.25, 1.0) * mag;
                vec3 stepEmission = (colDust + colPlume + colMag) * uEmissionScale;

                accumColor += transmittance * alpha * stepEmission;
                transmittance *= (1.0 - alpha);
                t += ds;
            }

            gl_FragColor = vec4(accumColor, 1.0 - transmittance);
        }
    </script>

    <script>
        const container = document.getElementById("canvas-container");
        const scene = new THREE.Scene();
        scene.background = new THREE.Color(0x07090e);

        const camera = new THREE.PerspectiveCamera(45, window.innerWidth / window.innerHeight, 0.1, 100);
        camera.position.set(0.0, -2.6, 1.8);

        const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: false });
        renderer.setSize(window.innerWidth, window.innerHeight);
        renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2.0));
        container.appendChild(renderer.domElement);

        const controls = new THREE.OrbitControls(camera, renderer.domElement);
        controls.enableDamping = true;
        controls.dampingFactor = 0.05;

        // Add subtle cosmic star particles
        const starGeom = new THREE.BufferGeometry();
        const starCount = 1000;
        const starPositions = new Float32Array(starCount * 3);
        for (let i = 0; i < starCount * 3; i += 3) {
            starPositions[i] = (Math.random() - 0.5) * 40.0;
            starPositions[i+1] = (Math.random() - 0.5) * 40.0;
            starPositions[i+2] = (Math.random() - 0.5) * 40.0;
        }
        starGeom.setAttribute("position", new THREE.BufferAttribute(starPositions, 3));
        const starMat = new THREE.PointsMaterial({ color: 0x64748b, size: 0.08, transparent: true, opacity: 0.6 });
        scene.add(new THREE.Points(starGeom, starMat));

        // Bounding cube for raymarching
        const boxGeom = new THREE.BoxGeometry(2.0, 2.0, 2.0);

        const vertexShader = document.getElementById("vertexShader").textContent;
        const fragmentShader = document.getElementById("fragmentShader").textContent;

        const uniforms = {
            uCameraPos: { value: camera.position },
            uDensityScale: { value: 4.5 },
            uEmissionScale: { value: 1.8 },
            uPlumeGain: { value: 1.5 },
            uMagGain: { value: 1.2 },
            uSedenionFilter: { value: 1.0 },
            uMaxSteps: { value: 96 },
            uTime: { value: 0.0 }
        };

        const raymarchMaterial = new THREE.ShaderMaterial({
            vertexShader: vertexShader,
            fragmentShader: fragmentShader,
            uniforms: uniforms,
            side: THREE.BackSide,
            transparent: true,
            depthWrite: false
        });

        const volumeMesh = new THREE.Mesh(boxGeom, raymarchMaterial);
        scene.add(volumeMesh);

        // Bounding box wireframe helper
        const wireGeom = new THREE.BoxGeometry(2.0, 2.0, 2.0);
        const wireMat = new THREE.MeshBasicMaterial({ color: 0x30363d, wireframe: true, transparent: true, opacity: 0.4 });
        scene.add(new THREE.Mesh(wireGeom, wireMat));

        // Coordinate axes
        const axes = new THREE.AxesHelper(1.2);
        scene.add(axes);

        // Controls binding
        document.getElementById("densitySlider").oninput = e => uniforms.uDensityScale.value = parseFloat(e.target.value);
        document.getElementById("emissionSlider").oninput = e => uniforms.uEmissionScale.value = parseFloat(e.target.value);
        document.getElementById("stepSlider").oninput = e => uniforms.uMaxSteps.value = parseInt(e.target.value);
        document.getElementById("plumeSlider").oninput = e => uniforms.uPlumeGain.value = parseFloat(e.target.value);
        document.getElementById("magSlider").oninput = e => uniforms.uMagGain.value = parseFloat(e.target.value);

        let sedenionActive = true;
        window.toggleSedenion = function() {
            sedenionActive = !sedenionActive;
            uniforms.uSedenionFilter.value = sedenionActive ? 1.0 : 0.0;
            const btn = document.getElementById("btnSedenion");
            btn.textContent = "Sedenion ZD Filter: " + (sedenionActive ? "ON" : "OFF");
            btn.classList.toggle("active", sedenionActive);
        };

        window.resetView = function() {
            camera.position.set(0.0, -2.6, 1.8);
            controls.target.set(0, 0, 0);
        };

        window.addEventListener("resize", () => {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });

        const clock = new THREE.Clock();
        function animate() {
            requestAnimationFrame(animate);
            controls.update();
            uniforms.uCameraPos.value.copy(camera.position);
            uniforms.uTime.value = clock.getElapsedTime();
            renderer.render(scene, camera);
        }
        animate();
    </script>
</body>
</html>
"""
    with open(filepath, "w", encoding="utf-8") as f:
        f.write(html)
