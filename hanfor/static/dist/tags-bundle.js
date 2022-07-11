(()=>{var e,a={692:(e,a,t)=>{var r=t(9755);t(1388),t(4712),t(3333),t(2993),t(944),t(3889),t(7312),t(2106),t(9570),t(7175);const n=t(9367),{SearchNode:o}=t(3024),{Modal:l}=t(4712);let c=sessionStorage.getItem("tag_search_string"),i=[":AND:",":OR:",":NOT:",":COL_INDEX_00:",":COL_INDEX_01:",":COL_INDEX_02:"];function s(){c=r("#search_bar").val().trim(),sessionStorage.setItem("tag_search_string",c),search_tree=o.fromQuery(c)}function d(e){let a=r(".modal-content");a.LoadingOverlay("show");let t=r("#tag_name").val(),n=r("#occurences").val();r.ajax({type:"DELETE",url:"api/tag/del_tag",data:{name:t,occurences:n},success:function(e){a.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):e.rebuild_table?location.reload():(tags_datatable.row(associated_row_id).data(e.data).draw(),l.getOrCreateInstance(document.getElementById("tag_modal")).hide())}})}r(document).ready((function(){let e=r("#tags_table"),a=e.DataTable({paging:!0,stateSave:!0,pageLength:50,responsive:!0,lengthMenu:[[10,50,100,500,-1],[10,50,100,500,"All"]],dom:'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',ajax:"api/tag/gets",deferRender:!0,columns:[{data:"name",render:function(e,a,t,r){return result='<a class="modal-opener" href="#">'+e+"</span></br>",result}},{data:"description",render:function(e,a,t,r){return result='<div class="white-space-pre">'+e+"</div>",result}},{data:"used_by",render:function(e,a,t,n){let o="";if(r(e).each((function(e,a){a.length>0&&(search_query="?command=search&col=2&q=%5C%22"+a+"%5C%22",o+='<span class="badge bg-info" style="background-color: '+t.color+'"><a href="'+base_url+search_query+'" target="_blank">'+a+"</a></span> ")})),e.length>1&&o.length>0){const e="?command=search&col=5&q="+t.name;o+='<span class="badge bg-info" style="background-color: #4275d8"><a href="./'+e+'" target="_blank">Show all</a></span> '}return o}},{data:"internal",render:function(e,a,t,r){return result='<input class="form-check-input" type="checkbox" '+(e?"checked":"")+">",result}},{data:"used_by",visible:!1,searchable:!1,render:function(e,a,t,n){return result="",r(e).each((function(e,a){a.length>0&&(result.length>1&&(result+=", "),result+=a)})),result}}],initComplete:function(){r("#search_bar").val(c),s(),r.fn.dataTable.ext.search.push((function(e,a,t){return function(e){return search_tree.evaluate(e,[!0,!0,!0])}(a)})),this.api().draw()}});a.column(4).visible(!1),new r.fn.dataTable.ColReorder(a,{});let t=r("#search_bar");t.keypress((function(e){13===e.which&&(s(),a.draw())})),new Awesomplete(t[0],{filter:function(e,a){let t=!1;return(a.split(":").length-1)%2==1&&(t=Awesomplete.FILTER_CONTAINS(e,a.match(/[^:]*$/)[0])),t},item:function(e,a){return Awesomplete.ITEM(e,a.match(/(:)([\S]*$)/)[2])},replace:function(e){const a=this.input.value.match(/(.*)(:(?!.*:).*$)/)[1];this.input.value=a+e},list:i,minChars:1,autoFirst:!0}),e.find("tbody").on("click","a.modal-opener",(function(e){e.preventDefault();let t=a.row(r(e.target).parent()).data(),n=a.row(r(e.target).parent()).index(),o=r(".modal-content");l.getOrCreateInstance(r("#tag_modal")).show(),r("#modal_associated_row_index").val(n),r("#tag_name_old").val(t.name),r("#occurences").val(t.used_by),r("#tag_modal_title").html("Tag: "+t.name),r("#tag_name").val(t.name),r("#tag_color").val(t.color),r("#tag-description").val(t.description),r("#tag_internal").prop("checked",t.internal),o.LoadingOverlay("hide")})),r("#save_tag_modal").click((function(){!function(e){let a=r(".modal-content");a.LoadingOverlay("show");let t=r("#tag_name").val(),n=r("#tag_name_old").val(),o=r("#occurences").val(),l=r("#tag_color").val(),c=parseInt(r("#modal_associated_row_index").val()),i=r("#tag-description").val(),s=r("#tag_internal").prop("checked");r.post("api/tag/update",{name:t,name_old:n,occurences:o,color:l,description:i,internal:s},(function(t){a.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):t.rebuild_table?location.reload():(e.row(c).data(t.data).draw(),r("#tag_modal").modal("hide"))}))}(a)})),r(".delete_tag").bootstrapConfirmButton({onConfirm:function(){d(r(this).attr("name"))}}),n(r("#tag-description")),r("#tag_modal").on("shown.bs.modal",(function(e){n.update(r("#tag-description"))})),r(".clear-all-filters").click((function(){r("#search_bar").val("").effect("highlight",{color:"green"},500),s(),a.draw()}))}))}},t={};function r(e){var n=t[e];if(void 0!==n)return n.exports;var o=t[e]={id:e,exports:{}};return a[e].call(o.exports,o,o.exports,r),o.exports}r.m=a,e=[],r.O=(a,t,n,o)=>{if(!t){var l=1/0;for(d=0;d<e.length;d++){for(var[t,n,o]=e[d],c=!0,i=0;i<t.length;i++)(!1&o||l>=o)&&Object.keys(r.O).every((e=>r.O[e](t[i])))?t.splice(i--,1):(c=!1,o<l&&(l=o));if(c){e.splice(d--,1);var s=n();void 0!==s&&(a=s)}}return a}o=o||0;for(var d=e.length;d>0&&e[d-1][2]>o;d--)e[d]=e[d-1];e[d]=[t,n,o]},r.n=e=>{var a=e&&e.__esModule?()=>e.default:()=>e;return r.d(a,{a}),a},r.d=(e,a)=>{for(var t in a)r.o(a,t)&&!r.o(e,t)&&Object.defineProperty(e,t,{enumerable:!0,get:a[t]})},r.o=(e,a)=>Object.prototype.hasOwnProperty.call(e,a),r.r=e=>{"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},r.j=81,(()=>{var e={81:0};r.O.j=a=>0===e[a];var a=(a,t)=>{var n,o,[l,c,i]=t,s=0;if(l.some((a=>0!==e[a]))){for(n in c)r.o(c,n)&&(r.m[n]=c[n]);if(i)var d=i(r)}for(a&&a(t);s<l.length;s++)o=l[s],r.o(e,o)&&e[o]&&e[o][0](),e[o]=0;return r.O(d)},t=self.webpackChunkhanfor=self.webpackChunkhanfor||[];t.forEach(a.bind(null,0)),t.push=a.bind(null,t.push.bind(t))})(),r.nc=void 0;var n=r.O(void 0,[351],(()=>r(692)));n=r.O(n)})();