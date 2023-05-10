from os import path
from setuptools import setup

here = path.abspath(path.dirname(__file__))

# Long description will be contents of README
with open(path.join(here, "README.md"), encoding="utf-8") as f:
    long_description = f.read()

setup(
    name="arachne",
    version="2023.04.30",
    description="Graph functionality in Chapel for use with Arkouda.",
    long_description=long_description,
    long_description_content_type="text/markdown",
    packages=["arachne"],
    python_requires=">=3.8",
    install_requires=["networkx","scipy"],
)