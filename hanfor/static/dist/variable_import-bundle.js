!function(t){function e(e){for(var n,s,i=e[0],l=e[1],c=e[2],d=0,p=[];d<i.length;d++)s=i[d],o[s]&&p.push(o[s][0]),o[s]=0;for(n in l)Object.prototype.hasOwnProperty.call(l,n)&&(t[n]=l[n]);for(u&&u(e);p.length;)p.shift()();return r.push.apply(r,c||[]),a()}function a(){for(var t,e=0;e<r.length;e++){for(var a=r[e],n=!0,i=1;i<a.length;i++){var l=a[i];0!==o[l]&&(n=!1)}n&&(r.splice(e--,1),t=s(s.s=a[0]))}return t}var n={},o={3:0},r=[];function s(e){if(n[e])return n[e].exports;var a=n[e]={i:e,l:!1,exports:{}};return t[e].call(a.exports,a,a.exports,s),a.l=!0,a.exports}s.m=t,s.c=n,s.d=function(t,e,a){s.o(t,e)||Object.defineProperty(t,e,{enumerable:!0,get:a})},s.r=function(t){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(t,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(t,"__esModule",{value:!0})},s.t=function(t,e){if(1&e&&(t=s(t)),8&e)return t;if(4&e&&"object"==typeof t&&t&&t.__esModule)return t;var a=Object.create(null);if(s.r(a),Object.defineProperty(a,"default",{enumerable:!0,value:t}),2&e&&"string"!=typeof t)for(var n in t)s.d(a,n,function(e){return t[e]}.bind(null,n));return a},s.n=function(t){var e=t&&t.__esModule?function(){return t.default}:function(){return t};return s.d(e,"a",e),e},s.o=function(t,e){return Object.prototype.hasOwnProperty.call(t,e)},s.p="./static/dist/";var i=window.webpackJsonp=window.webpackJsonp||[],l=i.push.bind(i);i.push=e,i=i.slice();for(var c=0;c<i.length;c++)e(i[c]);var u=l;r.push([221,0]),a()}({221:function(t,e,a){(function(t){a(24),a(13),a(22),a(12),a(156),a(21),a(20),a(19),a(18);let e=["bool","int","real","unknown","CONST","ENUM","ENUMERATOR"],n=!1;const{SearchNode:o}=a(17);let r=sessionStorage.getItem("var_import_search_string"),s=void 0,i=[!0,!0,!0,!0,!0,!0];function l(){r=t("#search_bar").val().trim(),sessionStorage.setItem("var_import_search_string",r),s=o.fromQuery(r)}function c(a,o,r){let s=t("#variable_modal"),i=t("#variable_value_form_group"),l=t(".enum-controls"),c=t("#constraints_container"),u=Object(),d=t("#variable_type"),p=t("#variable_value"),b=t("#save_variable_modal"),g="";d.prop("disabled",!0),p.prop("disabled",!0),b.hide(),n=!1,"source"===r?(u=a.source,g="Source Variable:"):"target"===r?(u=a.target,g="Target Variable:"):"result"===r&&(g="Resulting Variable:",u=a.result,d.prop("disabled",!1),p.prop("disabled",!1),b.show()),d.autocomplete({minLength:0,source:e}).on("focus",function(){t(this).keydown()}),t("#variable_modal_title").html(g+" <code>"+a.name+"</code>"),b.attr("data-name",a.name),d.val(u.type),i.hide(),l.hide(),c.hide(),"CONST"===u.type||"ENUMERATOR"===u.type?(i.show(),p.val(u.const_val)):"ENUM"===u.type&&(l.show(),t("#enumerators").html(""),function(e,a){let n=t("#enumerators");n.html("");let o="";a.rows().every(function(){let t=this.data();e.length<t.name.length&&t.name.startsWith(e)&&void 0!==t.result.name&&(o+="<p><code>"+t.name+"</code> : <code>"+t.result.const_val+"</code></p>")}),n.html(o)}(u.name,o)),function(e,a,n,o){function r(t,e=!1,a="none"){let n="";for(var o in t){let r=t[o];if(r.origin===a)if(e){let t="",e="";r.to_result?(t="Included in result (click to toggle).",e="btn-success"):(t="Not Included in result (click to toggle).",e="btn-secondary"),n+='<div class="constraint-element">',n+='<button type="button" data-type="'+a+'" data-constrid="'+r.id+'" class="btn '+e+' btn-sm constraint-handle">'+t+"</button>",n+="<pre>"+r.constraint+"</pre>",n+="</div>"}else n+="<pre>"+r.constraint+"</pre>"}return n}let s=t("#constraints_list"),i="";"result"===o?(void 0!==e.target.constraints&&e.target.constraints.length>0&&(i+="<h6>From Target</h6>",i+=r(e.available_constraints,!0,"target")),void 0!==e.source.constraints&&e.source.constraints.length>0&&(i+="<h6>From Source</h6>",i+=r(e.available_constraints,!0,"source"))):i+=r(e.available_constraints,!1,o),s.html(i),n.show()}(a,0,c,r),t(".constraint-handle").click(function(){n=!0;let e=t(this).attr("data-constrid"),r=t(this).closest("div").find("pre"),s=o.row("#"+a.name),i=s.data();r.effect("highlight",{color:"green"},800),t(this).toggleClass("btn-success"),t(this).toggleClass("btn-secondary"),t(this).hasClass("btn-success")?(t(this).html("Included in result (click to toggle)."),i.available_constraints[e].to_result=!0):(t(this).html("Not Included in result (click to toggle)."),i.available_constraints[e].to_result=!1),s.data(i)}),s.modal("show")}function u(t,e,a=!0,n=!0){let o=t.data();for(var r in"source"===e&&"source"!==o.action?void 0!==o.source.name&&(o.result=o.source,o.action="source"):"target"===e&&"target"!==o.action?void 0!==o.target.name&&(o.result=o.target,o.action="target"):"skip"===e&&(o.result=o.target,o.action=void 0!==o.target.name?"target":"skipped"),o.available_constraints){let t=o.available_constraints[r];o.available_constraints[r].to_result=t.origin===e}a?t.data(o).draw("full-hold"):t.data(o),n&&d(o)}function d(e=!1){let a=t("body");a.LoadingOverlay("show");let n=Object();e?n[e.name]={action:e.action}:t("#var_import_table").DataTable().rows({selected:!0}).every(function(){let t=this.data();n[t.name]={action:t.action}}),n=JSON.stringify(n),t.post("api/"+session_id+"/store_table",{rows:n},function(t){a.LoadingOverlay("hide",!0),!1===t.success&&alert(t.errormsg)})}function p(e,a){"apply-import"===a&&function(e){let a=t("body");a.LoadingOverlay("show"),t.post("api/"+session_id+"/apply_import",{},function(t){a.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):alert("Imported result variables.")})}(),"delete-session"===a&&function(){let e=t("body");e.LoadingOverlay("show"),t.post("api/"+session_id+"/delete_me",{id:session_id},function(t){e.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):window.location.href=base_url+"variables"})}()}t(document).ready(function(){let e=t("#var_import_table").DataTable({paging:!0,stateSave:!0,select:{style:"os",selector:"td:first-child"},pageLength:200,responsive:!0,lengthMenu:[[10,50,100,500,-1],[10,50,100,500,"All"]],dom:'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',ajax:"api/"+session_id+"/get_table_data",deferRender:!0,rowId:"name",columns:[{orderable:!1,className:"select-checkbox",targets:[0],data:null,defaultContent:""},{data:function(t,e,a,n){return t},targets:[1],orderable:!1,render:function(t,e,a,n){return'<div class="btn-group" role="group" aria-label="Basic example"><button type="button" data-action="skip" class="skip-btn btn btn-secondary'+("skipped"===t.action?" active":"")+'">Skip</button><button type="button" data-action="source" class="source-btn btn btn-secondary'+("source"===t.action?" active":"")+'">Source</button><button type="button" data-action="target" class="target-btn btn btn-secondary'+("target"===t.action?" active":"")+'">Target</button><button type="button" data-action="custom" class="custom-btn btn btn-secondary'+("custom"===t.action?" active":"")+'">Custom</button></div>'}},{data:function(t,e,a,n){return t},targets:[1],render:function(t,e,a,n){let o="";const r=void 0!==t.source.name,s=void 0!==t.target.name;return r&&s?(o+='<span class="badge badge-info">match_in_source_and_target</span>',t.source.type!==t.target.type?o+='<span class="badge badge-info">unmatched_types</span>':o+='<span class="badge badge-info">same_types</span>'):(r||(o+='<span class="badge badge-info">no_match_in_source</span>'),s||(o+='<span class="badge badge-info">no_match_in_target</span>')),r&&t.source.constraints.length>0&&(o+='<span class="badge badge-info">source_has_constraints</span>'),s&&t.target.constraints.length>0&&(o+='<span class="badge badge-info">target_has_constraints</span>'),o}},{data:function(t,e,a,n){return t.source},targets:[3],render:function(t,e,a,n){let o="";return o=void 0!==t.name?'<p class="var_link" data-type="source" style="cursor: pointer"><code>'+t.name+'</code> <span class="badge badge-info">'+t.type+"</span></p>":"No match."}},{data:function(t,e,a,n){return t.target},targets:[4],order:"asc",render:function(t,e,a,n){let o="";return o=void 0!==t.name?'<p class="var_link" data-type="target" style="cursor: pointer"><code>'+t.name+'</code><span class="badge badge-info">'+t.type+"</span>":"No match."}},{data:function(t,e,a,n){return t.result},targets:[5],render:function(t,e,a,n){let o="";return o=void 0!==t.name?'<p class="var_link" data-type="result" style="cursor: pointer"><code>'+t.name+'</code><span class="badge badge-info">'+t.type+"</span>":"Skipped."}}],infoCallback:function(e,a,n,o,r,s){var i=this.api().page.info();t("#clear-all-filters-text").html("Showing "+r+"/"+i.recordsTotal+". Clear all.");let l="Showing "+a+" to "+n+" of "+r+" entries";return l+=" (filtered from "+i.recordsTotal+" total entries)."},initComplete:function(){t("#search_bar").val(r),l(),t.fn.dataTable.ext.search.push(function(t,e,a){return function(t){return s.evaluate(t,i)}(e)}),this.api().draw(),t("#var_import_table").colResizable({liveDrag:!0,postbackSafe:!0})}});t("#search_bar").keypress(function(t){13===t.which&&(l(),e.draw())});let a=t("#var_import_table tbody");a.on("click",".var_link",function(a){a.preventDefault();let n=e.row(t(this).parents("tr")).data(),o=t(this).attr("data-type");c(n,e,o)}),t("#save_variable_modal").click(function(){let a=t(this).attr("data-name");!function(e,a){let o=t("#variable_modal"),r=t("#variable_type").val(),s=t("#variable_value").val(),i=a.data(),l=!1;i.result.type!==r&&(l=!0,i.result.type=r),"CONST"!==i.result.type&&"ENUMERATOR"!==i.result.type||i.result.const_val===s||(l=!0,i.result.const_val=s),l||n?(i.action="custom",o.LoadingOverlay("show"),t.post("api/"+session_id+"/store_variable",{row:JSON.stringify(i)},function(e){o.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):(a.data(i).draw("full-hold"),o.modal("hide"),t(a.node()).effect("highlight",{color:"green"},800))})):o.modal("hide")}(0,e.row("#"+a))}),t("#variable_type").on("change, focusout, keyup",function(){let e=t("#variable_value_form_group");["CONST","ENUMERATOR"].includes(t(this).val())?e.show():e.hide()}),a.on("click",".target-btn, .source-btn, .skip-btn",function(a){a.preventDefault(),u(e.row(t(this).parents("tr")),t(this).attr("data-action"))}),t(".select-all-button").on("click",function(a){t(this).hasClass("btn-secondary")?e.rows({page:"current"}).select():e.rows({page:"current"}).deselect(),t(".select-all-button").toggleClass("btn-secondary btn-primary")}),t(".action-btn").click(function(a){!function(t,e){t.rows({selected:!0}).every(function(){u(this,e,!1,!1)}),d()}(e,t(this).attr("data-action"))}),t("#delete_session_button").confirmation({rootSelector:"#delete_session_button"}),t(".tools-btn").click(function(e){p(0,t(this).attr("data-action"))}),e.on("user-select",function(){let e=t(".select-all-button");e.removeClass("btn-primary"),e.addClass("btn-secondary ")}),t(".clear-all-filters").click(function(){t("#search_bar").val("").effect("highlight",{color:"green"},500),l(),e.draw()})})}).call(this,a(4))}});