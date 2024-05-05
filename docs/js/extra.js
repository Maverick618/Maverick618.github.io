
// window.addEventListener('load', updateScheme, false);

const updateBoxFontColor = e => {
    var a = localStorage.getItem('data-md-color-scheme');
    if (a !== "default") {
        var elements = document.getElementsByClassName('box');
        for (var i in elements) {
            // alert(elements[i].style.color);
            elements[i].style.color = "white";
        }
    }
}

(() => {
    var p = localStorage.getItem("data-md-color-primary");
    if (p) {
        document.body.setAttribute('data-md-color-primary', p);
    }
    updateBoxFontColor();
})()