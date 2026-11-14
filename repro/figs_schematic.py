from pathlib import Path
import runpy

source = Path(__file__).with_name('draw_schematic_svg.py')
runpy.run_path(str(source), run_name='__main__')
