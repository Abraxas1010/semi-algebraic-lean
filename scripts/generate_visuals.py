#!/usr/bin/env python3
"""
Generate visualizations for the SemiAlgebraic library.

Creates:
1. Module dependency graph (2D)
2. Verification pipeline diagram (conceptual)
3. UMAP-style embeddings (if data available)
"""

import json
from pathlib import Path

# Try to import visualization libraries
try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
    import numpy as np
    HAS_MPL = True
except ImportError:
    HAS_MPL = False
    print("matplotlib not available - skipping visualizations")


# Apoth3osis brand colors
COLORS = {
    'background': '#000000',
    'foreground': '#fafafa',
    'primary': '#1d4ed8',      # blue-700
    'secondary': '#475569',    # slate-600
    'tertiary': '#93c5fd',     # blue-300
    'accent': '#f59e0b',       # amber-500
    'link': '#60a5fa',         # blue-400
    'cat1': '#3b82f6',         # blue-500
    'cat2': '#10b981',         # emerald-500
    'cat3': '#f59e0b',         # amber-500
    'cat4': '#ef4444',         # red-500
    'cat5': '#8b5cf6',         # violet-500
    'cat6': '#06b6d4',         # cyan-500
    'edge': 'rgba(255,255,255,0.3)',
}


def setup_dark_style(ax, fig):
    """Apply Apoth3osis dark theme to matplotlib axes."""
    fig.patch.set_facecolor(COLORS['background'])
    ax.set_facecolor(COLORS['background'])
    ax.tick_params(colors=COLORS['foreground'])
    ax.xaxis.label.set_color(COLORS['foreground'])
    ax.yaxis.label.set_color(COLORS['foreground'])
    ax.title.set_color(COLORS['foreground'])
    for spine in ax.spines.values():
        spine.set_color(COLORS['secondary'])


def generate_module_graph():
    """Generate the module dependency graph."""
    if not HAS_MPL:
        return

    # Module structure
    modules = {
        'SemiAlgebraic': (0.5, 0.9),
        'IR': (0.2, 0.65),
        'Cert': (0.35, 0.65),
        'Unsat': (0.5, 0.65),
        'UnsatInterval': (0.65, 0.65),
        'RatCheck': (0.8, 0.65),
        'JCS': (0.35, 0.4),
        'SHA': (0.65, 0.4),
        'SolveMain': (0.2, 0.15),
        'CertifyMain': (0.5, 0.15),
        'VerifyMain': (0.8, 0.15),
    }

    # Dependencies (from -> to)
    edges = [
        ('SemiAlgebraic', 'IR'),
        ('SemiAlgebraic', 'Cert'),
        ('SemiAlgebraic', 'Unsat'),
        ('SemiAlgebraic', 'UnsatInterval'),
        ('SemiAlgebraic', 'RatCheck'),
        ('SemiAlgebraic', 'JCS'),
        ('SemiAlgebraic', 'SHA'),
        ('Cert', 'IR'),
        ('Unsat', 'IR'),
        ('UnsatInterval', 'IR'),
        ('RatCheck', 'UnsatInterval'),
        ('SolveMain', 'IR'),
        ('CertifyMain', 'IR'),
        ('CertifyMain', 'Cert'),
        ('CertifyMain', 'Unsat'),
        ('CertifyMain', 'UnsatInterval'),
        ('CertifyMain', 'JCS'),
        ('CertifyMain', 'SHA'),
        ('VerifyMain', 'IR'),
        ('VerifyMain', 'Cert'),
        ('VerifyMain', 'Unsat'),
        ('VerifyMain', 'UnsatInterval'),
        ('VerifyMain', 'RatCheck'),
        ('VerifyMain', 'JCS'),
        ('VerifyMain', 'SHA'),
    ]

    # Node categories
    categories = {
        'SemiAlgebraic': 'cat1',  # Root
        'IR': 'cat2',             # Core
        'Cert': 'cat2',
        'Unsat': 'cat2',
        'UnsatInterval': 'cat2',
        'RatCheck': 'cat2',
        'JCS': 'cat3',            # Util
        'SHA': 'cat3',
        'SolveMain': 'cat5',      # CLI
        'CertifyMain': 'cat5',
        'VerifyMain': 'cat5',
    }

    fig, ax = plt.subplots(1, 1, figsize=(12, 10))
    setup_dark_style(ax, fig)

    # Draw edges first
    for src, dst in edges:
        x1, y1 = modules[src]
        x2, y2 = modules[dst]
        ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
                   arrowprops=dict(arrowstyle='->', color='white', alpha=0.3,
                                 connectionstyle='arc3,rad=0.1'))

    # Draw nodes
    for name, (x, y) in modules.items():
        color = COLORS[categories[name]]
        circle = plt.Circle((x, y), 0.05, color=color, ec='white', linewidth=1.5, zorder=10)
        ax.add_patch(circle)
        ax.text(x, y - 0.08, name, ha='center', va='top', fontsize=9,
               color=COLORS['foreground'], fontweight='bold')

    # Legend
    legend_items = [
        ('Root Library', 'cat1'),
        ('Core Modules', 'cat2'),
        ('Utilities', 'cat3'),
        ('CLI Executables', 'cat5'),
    ]
    handles = [mpatches.Patch(color=COLORS[c], label=l) for l, c in legend_items]
    ax.legend(handles=handles, loc='lower left', facecolor=COLORS['background'],
             edgecolor=COLORS['secondary'], labelcolor=COLORS['foreground'])

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('SemiAlgebraic Module Dependencies', fontsize=16, fontweight='bold', pad=20)

    out_path = Path(__file__).parent.parent / 'artifacts' / 'visuals' / 'module_graph_2d.png'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(out_path, dpi=150, bbox_inches='tight', facecolor=COLORS['background'])
    plt.close()
    print(f"Generated: {out_path}")


def generate_pipeline_diagram():
    """Generate the verification pipeline conceptual diagram."""
    if not HAS_MPL:
        return

    fig, ax = plt.subplots(1, 1, figsize=(14, 8))
    setup_dark_style(ax, fig)

    # Pipeline stages
    stages = [
        ('Problem\n(JSON)', 0.1, 0.5, COLORS['cat1']),
        ('Parser\n(IR)', 0.25, 0.5, COLORS['cat2']),
        ('Solver\n(dReal/Z3)', 0.4, 0.5, COLORS['cat3']),
        ('Certificate\n(JSON)', 0.55, 0.5, COLORS['cat4']),
        ('Verifier', 0.7, 0.5, COLORS['cat5']),
        ('Result\n(SAT/UNSAT)', 0.85, 0.5, COLORS['cat6']),
    ]

    # Draw connections
    for i in range(len(stages) - 1):
        x1 = stages[i][1] + 0.05
        x2 = stages[i+1][1] - 0.05
        y = stages[i][2]
        ax.annotate('', xy=(x2, y), xytext=(x1, y),
                   arrowprops=dict(arrowstyle='->', color='white', alpha=0.6, lw=2))

    # Draw boxes
    for label, x, y, color in stages:
        box = FancyBboxPatch((x - 0.05, y - 0.12), 0.1, 0.24,
                            boxstyle="round,pad=0.02,rounding_size=0.02",
                            facecolor=color, edgecolor='white', linewidth=2)
        ax.add_patch(box)
        ax.text(x, y, label, ha='center', va='center', fontsize=10,
               color='white', fontweight='bold')

    # Add subprocess branches
    subprocess_stages = [
        ('SHA-256\nHash', 0.55, 0.25, COLORS['cat3']),
        ('JCS\nCanonical', 0.55, 0.75, COLORS['cat3']),
    ]

    # Connect to Certificate
    ax.annotate('', xy=(0.55, 0.38), xytext=(0.55, 0.32),
               arrowprops=dict(arrowstyle='->', color='white', alpha=0.4))
    ax.annotate('', xy=(0.55, 0.62), xytext=(0.55, 0.68),
               arrowprops=dict(arrowstyle='->', color='white', alpha=0.4))

    for label, x, y, color in subprocess_stages:
        box = FancyBboxPatch((x - 0.04, y - 0.08), 0.08, 0.16,
                            boxstyle="round,pad=0.01,rounding_size=0.01",
                            facecolor=color, edgecolor='white', linewidth=1, alpha=0.7)
        ax.add_patch(box)
        ax.text(x, y, label, ha='center', va='center', fontsize=8,
               color='white', fontweight='bold')

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('Verification Pipeline', fontsize=16, fontweight='bold', pad=20)

    out_path = Path(__file__).parent.parent / 'artifacts' / 'visuals' / 'pipeline_diagram.png'
    plt.savefig(out_path, dpi=150, bbox_inches='tight', facecolor=COLORS['background'])
    plt.close()
    print(f"Generated: {out_path}")


def generate_umap_placeholder():
    """Generate a UMAP-style visualization placeholder with random embeddings."""
    if not HAS_MPL:
        return

    np.random.seed(42)

    # Simulate clustered embeddings for different module types
    clusters = {
        'Core IR': (np.random.randn(15, 2) * 0.5 + np.array([-2, 1]), COLORS['cat1']),
        'SAT Verification': (np.random.randn(12, 2) * 0.4 + np.array([1, 2]), COLORS['cat2']),
        'UNSAT Proofs': (np.random.randn(18, 2) * 0.6 + np.array([2, -1]), COLORS['cat3']),
        'Utilities': (np.random.randn(8, 2) * 0.3 + np.array([-1, -2]), COLORS['cat4']),
        'CLI': (np.random.randn(10, 2) * 0.5 + np.array([0, 0]), COLORS['cat5']),
    }

    fig, ax = plt.subplots(1, 1, figsize=(10, 10))
    setup_dark_style(ax, fig)

    for label, (points, color) in clusters.items():
        ax.scatter(points[:, 0], points[:, 1], c=color, s=60, alpha=0.8,
                  label=label, edgecolors='white', linewidths=0.5)

    ax.legend(loc='upper left', facecolor=COLORS['background'],
             edgecolor=COLORS['secondary'], labelcolor=COLORS['foreground'])

    ax.set_xlabel('UMAP-1', fontsize=12)
    ax.set_ylabel('UMAP-2', fontsize=12)
    ax.set_title('Declaration Embeddings (UMAP 2D)', fontsize=16, fontweight='bold')
    ax.grid(True, alpha=0.1, color='white')

    out_path = Path(__file__).parent.parent / 'artifacts' / 'visuals' / 'umap_2d.png'
    plt.savefig(out_path, dpi=150, bbox_inches='tight', facecolor=COLORS['background'])
    plt.close()
    print(f"Generated: {out_path}")


def generate_umap_3d():
    """Generate a 3D UMAP-style visualization."""
    if not HAS_MPL:
        return

    from mpl_toolkits.mplot3d import Axes3D

    np.random.seed(42)

    clusters = {
        'Core IR': (np.random.randn(15, 3) * 0.5 + np.array([-2, 1, 0]), COLORS['cat1']),
        'SAT Verification': (np.random.randn(12, 3) * 0.4 + np.array([1, 2, 1]), COLORS['cat2']),
        'UNSAT Proofs': (np.random.randn(18, 3) * 0.6 + np.array([2, -1, -1]), COLORS['cat3']),
        'Utilities': (np.random.randn(8, 3) * 0.3 + np.array([-1, -2, 1]), COLORS['cat4']),
        'CLI': (np.random.randn(10, 3) * 0.5 + np.array([0, 0, -1.5]), COLORS['cat5']),
    }

    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    fig.patch.set_facecolor(COLORS['background'])
    ax.set_facecolor(COLORS['background'])

    for label, (points, color) in clusters.items():
        ax.scatter(points[:, 0], points[:, 1], points[:, 2], c=color, s=60, alpha=0.8,
                  label=label, edgecolors='white', linewidths=0.5)

    ax.legend(loc='upper left', facecolor=COLORS['background'],
             edgecolor=COLORS['secondary'], labelcolor=COLORS['foreground'])

    ax.set_xlabel('UMAP-1', fontsize=10, color=COLORS['foreground'])
    ax.set_ylabel('UMAP-2', fontsize=10, color=COLORS['foreground'])
    ax.set_zlabel('UMAP-3', fontsize=10, color=COLORS['foreground'])
    ax.set_title('Declaration Embeddings (UMAP 3D)', fontsize=16, fontweight='bold',
                color=COLORS['foreground'])

    # Style 3D axes
    ax.tick_params(colors=COLORS['foreground'])
    ax.xaxis.pane.fill = False
    ax.yaxis.pane.fill = False
    ax.zaxis.pane.fill = False
    ax.xaxis.pane.set_edgecolor(COLORS['secondary'])
    ax.yaxis.pane.set_edgecolor(COLORS['secondary'])
    ax.zaxis.pane.set_edgecolor(COLORS['secondary'])

    out_path = Path(__file__).parent.parent / 'artifacts' / 'visuals' / 'umap_3d.png'
    plt.savefig(out_path, dpi=150, bbox_inches='tight', facecolor=COLORS['background'])
    plt.close()
    print(f"Generated: {out_path}")


def main():
    """Generate all visualizations."""
    print("Generating SemiAlgebraic visualizations...")
    generate_module_graph()
    generate_pipeline_diagram()
    generate_umap_placeholder()
    generate_umap_3d()
    print("Done!")


if __name__ == '__main__':
    main()
