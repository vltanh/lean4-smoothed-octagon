"""The shared look of the paper's figures: matplotlib settings, colours and sizes.

Every figure module calls `setup()` before drawing and saves with `save(fig, path)`.
"""
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402

# Full text width of the amsart page with 11pt type, in inches, and a half-width panel.
FULL = 6.3
HALF = 3.05

INK = '#1f2328'
FAINT = '#8c959f'
GRID = '#d0d7de'
BLUE = '#1f6feb'
ORANGE = '#d4721a'
GREEN = '#2e8b57'
PURPLE = '#7b4fc0'
RED = '#c0392b'
FILL = '#dbe9fb'
# The colours of the vertex controls e_0, e_1, e_2 (labels 0, 1, 2), used in every figure that
# shows a switching word.
CONTROL_COLORS = (ORANGE, PURPLE, GREEN)


def setup():
    plt.rcParams.update({
        'font.family': 'serif',
        'font.serif': ['Latin Modern Roman', 'CMU Serif', 'DejaVu Serif'],
        'mathtext.fontset': 'cm',
        'font.size': 9,
        'axes.labelsize': 9,
        'axes.titlesize': 9,
        'legend.fontsize': 8,
        'xtick.labelsize': 8,
        'ytick.labelsize': 8,
        'axes.edgecolor': INK,
        'axes.linewidth': 0.6,
        'lines.linewidth': 1.2,
        'savefig.bbox': 'tight',
        'savefig.pad_inches': 0.02,
        'pdf.fonttype': 42,
    })


def save(fig, path):
    fig.savefig(path)
    plt.close(fig)
